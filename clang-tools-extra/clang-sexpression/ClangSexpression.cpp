#include "clang/AST/ASTNodeTraverser.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/TextNodeDumper.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/CommandLine.h"

#include <fnmatch.h>

using namespace clang::tooling;
using namespace clang;

#define DISPATCH_STMT(X)                                                       \
  case Stmt::StmtClass::X##Class:                                              \
    locationDebug(range);                                                      \
    return Visit##X((X *)stmt);

#define DISPATCH_DECL(X)                                                       \
  case Decl::Kind::X:                                                          \
    locationDebug(decl->getSourceRange());                                     \
    return Visit##X((X##Decl *)decl);

#define TRANSPARENT_STMT(X)                                                    \
  case Stmt::StmtClass::X##Class:                                              \
    return VisitTransparentStmt(stmt);

#define IGNORE_DECL(X)                                                         \
  case Decl::Kind::X:                                                          \
    return;

#define RECURSE_CHILDREN_STMT(X)                                               \
  do {                                                                         \
    for (auto *it : X->children())                                             \
      DispatchStmt(it);                                                        \
  } while (0)

static llvm::cl::OptionCategory ClangSexpCategory("clang-sexpression options");

static llvm::cl::opt<bool> DontPrintRoot(
    "dont-print-root",
    llvm::cl::desc("Don't add a ROOT node at the root of the s-expression."),
    llvm::cl::init(false), llvm::cl::cat(ClangSexpCategory));

static llvm::cl::opt<bool> DebugOutput("debug-output",
                                       llvm::cl::desc("Output debug info"),
                                       llvm::cl::init(false),
                                       llvm::cl::cat(ClangSexpCategory));

static llvm::cl::opt<std::string> OutputFile("o", llvm::cl::desc("Output file"),
                                             llvm::cl::init("-"),
                                             llvm::cl::cat(ClangSexpCategory));

static llvm::cl::opt<std::string>
    DebugOutputFile("debug-o", llvm::cl::desc("Debug output file"),
                    llvm::cl::init("-"), llvm::cl::cat(ClangSexpCategory));

static llvm::cl::extrahelp CommonHelp(CommonOptionsParser::HelpMessage);

static llvm::cl::extrahelp
    MoreHelp("\nThis tool converts clang ASTs to S-Expressions\n");

static std::shared_ptr<llvm::raw_ostream> OutputStream;
static std::shared_ptr<llvm::raw_ostream> DebugOutputStream;

class SexpVisitor {
public:
  void printType(QualType t, const SourceRange &range) {
    locationDebug(range);
    *OutputStream << "\"" << t.getAsString() << "\"";
  }

  void VisitTranslationUnit(TranslationUnitDecl *tu) {
    // TranslationUnit are handled in the Consumer to make printing the filename
    // easier.
    for (auto dec : tu->decls())
      DispatchDecl(dec);
  }

  void VisitTransparentStmt(Stmt *stmt) { RECURSE_CHILDREN_STMT(stmt); }

  void VisitDecl(Decl *decl) {
    *OutputStream << '(' << decl->getDeclKindName() << ' ';

    if (decl->hasBody())
      DispatchStmt(decl->getBody());

    *OutputStream << ')';
  }

  void VisitFunction(const FunctionDecl *f) {
    if (!f->hasBody())
      return;

    // 2, because they're not printed in the DispatchDecl function.
    locationDebug(f->getBody(f)->getSourceRange(), 2);

    *OutputStream << "(Function " << f->getNameAsString() << ' ';

    printType(f->getType(), f->getSourceRange());
    *OutputStream << "(FunctionParameters ";

    locationDebug(f->getSourceRange());
    for (auto param : f->parameters())
      DispatchDecl((ParmVarDecl *)param);
    *OutputStream << ')';

    DispatchStmt(f->getBody());

    *OutputStream << ')';
  }

  void VisitFunctionTemplate(FunctionTemplateDecl *ft) {
    *OutputStream << "(FunctionTemplate " << ft->getNameAsString() << ' ';
    locationDebug(ft->getSourceRange());
    VisitFunction(ft->getTemplatedDecl());
    *OutputStream << ')';
  }

  void VisitParmVar(ParmVarDecl *p) {
    *OutputStream << "(ParmVarDecl " << p->getNameAsString() << ' ';
    locationDebug(p->getSourceRange());
    printType(p->getType(), p->getSourceRange());
    *OutputStream << ')';
  }

  void VisitTypedef(TypedefDecl *td) {
    *OutputStream << "(Typedef " << td->getNameAsString() << ' ';
    locationDebug(td->getSourceRange());
    printType(td->getUnderlyingType(), td->getSourceRange());
    *OutputStream << ')';
  }

  void VisitRecord(RecordDecl *rd) {
    *OutputStream << "(Record " << rd->getNameAsString() << ' ';
    locationDebug(rd->getSourceRange());
    for (auto *field : rd->fields())
      DispatchDecl(field);
    *OutputStream << ')';
  }

  void VisitField(FieldDecl *fd) {
    *OutputStream << '(' << fd->getNameAsString() << ' ';
    printType(fd->getType(), fd->getSourceRange());
    *OutputStream << ')';
  }

  void VisitEnum(EnumDecl *ed) {
    *OutputStream << "(Enum " << ed->getNameAsString();
    locationDebug(ed->getSourceRange());
    for (auto *field : ed->enumerators())
      DispatchDecl(field);
    *OutputStream << ')';
  }

  void VisitEnumConstant(EnumConstantDecl *ecd) {
    *OutputStream << '(' << ecd->getNameAsString() << ' '
                  << ecd->getInitVal().getExtValue() << ')';
    locationDebug(ecd->getSourceRange());
  }

  void VisitVar(VarDecl *vd) {
    *OutputStream << "(VarDecl " << vd->getNameAsString() << ' ';
    locationDebug(vd->getSourceRange());
    DispatchStmt(vd->getInit());
    printType(vd->getType(), vd->getSourceRange());
    *OutputStream << ')';
  }

  void VisitCXXRecord(CXXRecordDecl *cxxd) {
    *OutputStream << '(';
    if (cxxd->isUnion())
      *OutputStream << "Union";
    else if (cxxd->isClass())
      *OutputStream << "Class";
    else if (cxxd->isStruct())
      *OutputStream << "Struct";
    else
      *OutputStream << "CXXRecordDecl";

    locationDebug(cxxd->getSourceRange());
    *OutputStream << ' ' << cxxd->getNameAsString() << ' ';

    *OutputStream << "(CXXRecordFields ";
    locationDebug(cxxd->getSourceRange());
    for (auto *field : cxxd->fields())
      DispatchDecl(field);
    *OutputStream << ')';

    *OutputStream << "(CXXRecordMethods ";
    locationDebug(cxxd->getSourceRange());
    for (auto *method : cxxd->methods())
      DispatchDecl(method);
    *OutputStream << ')';

    *OutputStream << ')';
  }

  void VisitCXXMethod(CXXMethodDecl *cxxmd) {
    *OutputStream << "(CXXMethod " << cxxmd->getNameAsString() << ' ';
    locationDebug(cxxmd->getSourceRange());

    printType(cxxmd->getType(), cxxmd->getSourceRange());
    *OutputStream << "(CXXMethodParameters";
    locationDebug(cxxmd->getSourceRange());
    for (auto *param : cxxmd->parameters())
      DispatchDecl((ParmVarDecl *)param);
    *OutputStream << ')';
    DispatchStmt(cxxmd->getBody());

    *OutputStream << ')';
  }

  void DispatchDecl(Decl *decl) {
    if (!decl)
      return;

    if (!decl->getLocation().isValid())
      return;

    if (_sourceManager->isInSystemMacro(decl->getLocation()))
      return;

    if (_sourceManager->isInSystemHeader(decl->getLocation()))
      return;

    if (_sourceManager->getFilename(decl->getLocation()).endswith(".h"))
      return;

    if (_sourceManager->getFilename(decl->getLocation()).endswith(".hh"))
      return;

    switch (decl->getKind()) {
    case Decl::Kind::Function:
      return VisitFunction((FunctionDecl *)decl);
      DISPATCH_DECL(CXXMethod)
      DISPATCH_DECL(FunctionTemplate)
      DISPATCH_DECL(Typedef)
      DISPATCH_DECL(Record)
      DISPATCH_DECL(Field)
      DISPATCH_DECL(Enum)
      DISPATCH_DECL(EnumConstant)
      DISPATCH_DECL(Var)
      DISPATCH_DECL(CXXRecord)
      DISPATCH_DECL(ParmVar)
      DISPATCH_DECL(ClassTemplate)
      IGNORE_DECL(LinkageSpec)
    default:
      locationDebug(decl->getSourceRange());
      return VisitDecl(decl);
    }
  }

  void VisitClassTemplate(ClassTemplateDecl *ctd) {
    *OutputStream << "(ClassTemplateDecl ";

    VisitCXXRecord(ctd->getTemplatedDecl());

    *OutputStream << ')';
  }

  void VisitSwitchStmt(SwitchStmt *ss) {
    *OutputStream << "(SwitchStmt ";
    RECURSE_CHILDREN_STMT(ss);
    *OutputStream << ')';
  }

  void VisitGCCAsmStmt(GCCAsmStmt *as) {
    *OutputStream << "(GCCAsmStmt ";
    *OutputStream << '"' << as->getAsmString()->getString() << '"';
    locationDebug(as->getSourceRange());
    *OutputStream << ')';
  }

  void DispatchStmt(Stmt *stmt) {
    if (!stmt)
      return;

    auto range = stmt->getSourceRange();
    if (!range.getBegin().isValid())
      return;

    if (_sourceManager->isInSystemMacro(range.getBegin())) {
      // Don't expand system macros, but print them as is.
      locationDebug(range);
      *OutputStream << '"'
                    << Lexer::getSourceText(
                           CharSourceRange::getTokenRange(range),
                           *_sourceManager, LangOptions(), 0)
                    << '"';
      return;
    }

    switch (stmt->getStmtClass()) {
      DISPATCH_STMT(BinaryOperator)
      DISPATCH_STMT(UnaryOperator)
      DISPATCH_STMT(IntegerLiteral)
      DISPATCH_STMT(StringLiteral)
      DISPATCH_STMT(DeclStmt)
      DISPATCH_STMT(DeclRefExpr)
      DISPATCH_STMT(MemberExpr)
      DISPATCH_STMT(SwitchStmt)
      DISPATCH_STMT(CompoundAssignOperator)
      DISPATCH_STMT(GCCAsmStmt)
      TRANSPARENT_STMT(ParenExpr)
      TRANSPARENT_STMT(ExprWithCleanups)
      TRANSPARENT_STMT(MaterializeTemporaryExpr)
      TRANSPARENT_STMT(ImplicitCastExpr)
    default:
      locationDebug(range);
      return VisitStmt(stmt);
    }
  }

  void VisitCompoundAssignOperator(CompoundAssignOperator *cao) {
    *OutputStream << "(CompoundAssignOperator " << cao->getOpcodeStr().data()
                  << ' ';
    locationDebug(cao->getSourceRange());
    RECURSE_CHILDREN_STMT(cao);
    *OutputStream << ')';
  }

  void VisitMemberExpr(MemberExpr *me) {
    *OutputStream << "(MemberExpr ";
    RECURSE_CHILDREN_STMT(me);
    *OutputStream << me->getMemberDecl()->getNameAsString() << ')';
    locationDebug(me->getMemberDecl()->getSourceRange());
  }

  void VisitDeclStmt(DeclStmt *stmt) {
    if (stmt->isSingleDecl()) {
      *OutputStream << "(DeclStmt ";
      if (auto *var = dyn_cast<VarDecl>(stmt->getSingleDecl()))
        DispatchDecl(var);
      else {
        *OutputStream << stmt->getSingleDecl()->getDeclKindName();
        locationDebug(stmt->getSingleDecl()->getSourceRange());
      }

      *OutputStream << ')';
    }
  }

  void VisitIntegerLiteral(IntegerLiteral *i) {
    *OutputStream << "(IntegerLiteral " << i->getValue().getLimitedValue()
                  << ' ';
    locationDebug(i->getSourceRange());
    printType(i->getType(), i->getSourceRange());
    *OutputStream << ")";
  }

  void VisitStringLiteral(StringLiteral *s) {
    *OutputStream << "(StringLiteral ";
    s->outputString(*OutputStream);
    locationDebug(s->getSourceRange());
    *OutputStream << ")";
  }

  void VisitDeclRefExpr(DeclRefExpr *ref) {
    *OutputStream << '(' << ref->getDecl()->getNameAsString() << ')';
  }

  void VisitUnaryOperator(UnaryOperator *op) {
    *OutputStream << "(UnaryOperator "
                  << UnaryOperator::getOpcodeStr(op->getOpcode()).data() << ' ';
    locationDebug(op->getSourceRange());
    DispatchStmt(op->getSubExpr());
    *OutputStream << ')';
  }

  void VisitBinaryOperator(BinaryOperator *op) {
    *OutputStream << "(BinaryOperator " << op->getOpcodeStr().data() << ' ';
    locationDebug(op->getSourceRange());

    DispatchStmt(op->getLHS());
    DispatchStmt(op->getRHS());

    *OutputStream << ')';
  }

  void VisitStmt(Stmt *stmt) {
    *OutputStream << '(' << stmt->getStmtClassName();

    RECURSE_CHILDREN_STMT(stmt);

    *OutputStream << ')';
  }

  void setSourceManager(SourceManager *SM) { _sourceManager = SM; }

private:
  void locationDebug(const SourceRange &range, int count = 1) {
    if (!DebugOutput)
      return;

    for (int i = 0; i < count; i++) {
      range.getBegin().print(*DebugOutputStream, *_sourceManager);
      *DebugOutputStream << ' ';
      range.getEnd().print(*DebugOutputStream, *_sourceManager);
      *DebugOutputStream << '\n';
    }
  }

  SourceManager *_sourceManager;
};

class SexpConsumer : public ASTConsumer {
public:
  virtual void HandleTranslationUnit(ASTContext &Context) {
    _visitor.setSourceManager(&Context.getSourceManager());

    if (DebugOutput) {
      *DebugOutputStream << _file << ":begin " << _file << ":end\n";
      *DebugOutputStream << _file << ":begin " << _file << ":end\n";
    }

    *OutputStream << "(TranslationUnit \"" << _file << "\" ";
    _visitor.VisitTranslationUnit(Context.getTranslationUnitDecl());
    *OutputStream << ')';
  }

  SexpConsumer(StringRef file)
      : ASTConsumer(), _file(file.str()), _visitor(SexpVisitor{}) {}

private:
  std::string _file;
  SexpVisitor _visitor;
};

class SexpAction : public ASTFrontendAction {
public:
  virtual std::unique_ptr<ASTConsumer>
  CreateASTConsumer(CompilerInstance &Compiler, StringRef InFile) {
    (void)Compiler;

    return std::unique_ptr<ASTConsumer>(new SexpConsumer(InFile));
  }
};

int main(int argc, const char **argv) {
  CommonOptionsParser OptionsParser(argc, argv, ClangSexpCategory);
  auto compilationDatabaseFiles = OptionsParser.getCompilations().getAllFiles();

  ClangTool Tool(OptionsParser.getCompilations(),
                 OptionsParser.getSourcePathList());

  if (OutputFile == "-" && DebugOutputFile == "-" && DebugOutput) {
    llvm::errs() << "Can't set the debug and output files to stdout.";
    return 1;
  }

  std::error_code err;
  if (DebugOutput) {
    if (DebugOutputFile != "-")
      DebugOutputStream =
          std::make_shared<llvm::raw_fd_ostream>(DebugOutputFile, err);
    else
      DebugOutputStream.reset(&llvm::outs(), [](llvm::raw_ostream *a) {});
  }

  if (OutputFile != "-")
    OutputStream = std::make_shared<llvm::raw_fd_ostream>(OutputFile, err);
  else
    OutputStream.reset(&llvm::outs(), [](llvm::raw_ostream *a) {});

  if (!DontPrintRoot) {
    *OutputStream << "(ROOT ";
    if (DebugOutput) {
      *DebugOutputStream << "root:begin root:end\n";
    }
  }
  auto ret = Tool.run(newFrontendActionFactory<SexpAction>().get());
  if (!DontPrintRoot) {
    *OutputStream << ")";
  }

  return ret;
}
