#include "clang/AST/ASTNodeTraverser.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/TextNodeDumper.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/CommandLine.h"

#include <queue>
#include <stack>
#include <utility>

using namespace clang::tooling;
using namespace clang;

#define DISPATCH_STMT(X)                                                       \
  case Stmt::StmtClass::X##Class:                                              \
    return Visit##X((X *)stmt);

#define DISPATCH_DECL(X)                                                       \
  case Decl::Kind::X:                                                          \
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

void printType(QualType t) { llvm::outs() << "\"" << t.getAsString() << "\""; }

class SexpVisitor {
public:
  void VisitTranslationUnit(TranslationUnitDecl *tu) {
    // TranslationUnit are handled in the Consumer to make printing the filename
    // easier.
    for (auto dec : tu->decls())
      DispatchDecl(dec);
  }

  void VisitTransparentStmt(Stmt *stmt) { RECURSE_CHILDREN_STMT(stmt); }

  void VisitDecl(Decl *decl) {
    llvm::outs() << '(' << decl->getDeclKindName() << ' ';

    if (decl->hasBody())
      DispatchStmt(decl->getBody());

    llvm::outs() << ')';
  }

  void VisitFunction(FunctionDecl *f) {
    if (!f->hasBody())
      return;

    llvm::outs() << "(Function " << f->getNameAsString() << ' ';

    printType(f->getType());
    llvm::outs() << "(FunctionParameters ";
    for (auto param : f->parameters())
      VisitParmVarDecl((ParmVarDecl *)param);
    llvm::outs() << ')';

    DispatchStmt(f->getBody());

    llvm::outs() << ')';
  }

  void VisitFunctionTemplate(FunctionTemplateDecl *ft) {
    llvm::outs() << "(FunctionTemplate " << ft->getNameAsString() << ' ';
    VisitFunction(ft->getTemplatedDecl());
    llvm::outs() << ')';
  }

  void VisitParmVarDecl(ParmVarDecl *p) {
    llvm::outs() << "(ParmVarDecl " << p->getNameAsString() << ' ';
    printType(p->getType());
    llvm::outs() << ')';
  }

  void VisitTypedef(TypedefDecl *td) {
    llvm::outs() << "(Typedef " << td->getNameAsString() << ' ';
    printType(td->getUnderlyingType());
    llvm::outs() << ')';
  }

  void VisitRecord(RecordDecl *rd) {
    llvm::outs() << "(Record " << rd->getNameAsString() << ' ';
    for (auto *field : rd->fields())
      DispatchDecl(field);
    llvm::outs() << ')';
  }

  void VisitField(FieldDecl *fd) {
    llvm::outs() << '(' << fd->getNameAsString() << ' ';
    printType(fd->getType());
    llvm::outs() << ')';
  }

  void VisitEnum(EnumDecl *ed) {
    llvm::outs() << "(Enum " << ed->getNameAsString();
    for (auto *field : ed->enumerators())
      DispatchDecl(field);
    llvm::outs() << ')';
  }

  void VisitEnumConstant(EnumConstantDecl *ecd) {
    llvm::outs() << '(' << ecd->getNameAsString() << ' '
                 << ecd->getInitVal().getExtValue() << ')';
  }

  void VisitVar(VarDecl *vd) {
    llvm::outs() << "(VarDecl " << vd->getNameAsString() << ' ';
    DispatchStmt(vd->getInit());
    printType(vd->getType());
    llvm::outs() << ')';
  }

  void VisitCXXRecord(CXXRecordDecl *cxxd) {
    llvm::outs() << '(';
    if (cxxd->isUnion())
      llvm::outs() << "Union";
    else if (cxxd->isClass())
      llvm::outs() << "Class";
    else if (cxxd->isStruct())
      llvm::outs() << "Struct";
    else
      llvm::outs() << "CXXRecordDecl";

    llvm::outs() << ' ' << cxxd->getNameAsString() << ' ';

    llvm::outs() << "(CXXRecordFields ";
    for (auto *field : cxxd->fields())
      DispatchDecl(field);
    llvm::outs() << ')';

    llvm::outs() << "(CXXRecordMethods ";
    for (auto *method : cxxd->methods())
      DispatchDecl(method);
    llvm::outs() << ')';

    llvm::outs() << ')';
  }

  void VisitCXXMethod(CXXMethodDecl *cxxmd) {
    llvm::outs() << "(CXXMethod " << cxxmd->getNameAsString() << ' ';

    printType(cxxmd->getType());
    llvm::outs() << "(CXXMethodParameters";
    for (auto *param : cxxmd->parameters())
      VisitParmVarDecl((ParmVarDecl *)param);
    llvm::outs() << ')';
    DispatchStmt(cxxmd->getBody());

    llvm::outs() << ')';
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

    switch (decl->getKind()) {
      DISPATCH_DECL(Function)
      DISPATCH_DECL(CXXMethod)
      DISPATCH_DECL(FunctionTemplate)
      DISPATCH_DECL(Typedef)
      DISPATCH_DECL(Record)
      DISPATCH_DECL(Field)
      DISPATCH_DECL(Enum)
      DISPATCH_DECL(EnumConstant)
      DISPATCH_DECL(Var)
      DISPATCH_DECL(CXXRecord)
      DISPATCH_DECL(ClassTemplate)
      IGNORE_DECL(LinkageSpec)
    default:
      return VisitDecl(decl);
    }
  }

  void VisitClassTemplate(ClassTemplateDecl *ctd) {
    llvm::outs() << "(ClassTemplateDecl ";

    VisitCXXRecord(ctd->getTemplatedDecl());

    llvm::outs() << ')';
  }

  void VisitSwitchStmt(SwitchStmt *ss) {
    llvm::outs() << "(SwitchStmt ";
    RECURSE_CHILDREN_STMT(ss);
    llvm::outs() << ')';
  }

  void DispatchStmt(Stmt *stmt) {
    if (!stmt)
      return;

    auto range = stmt->getSourceRange();
    if (!range.getBegin().isValid())
      return;

    if (_sourceManager->isInSystemMacro(range.getBegin())) {
      // Don't expand system macros, but print them as is.
      llvm::outs() << '"'
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
      TRANSPARENT_STMT(ParenExpr)
      TRANSPARENT_STMT(ExprWithCleanups)
      TRANSPARENT_STMT(MaterializeTemporaryExpr)
      TRANSPARENT_STMT(ImplicitCastExpr)
    default:
      return VisitStmt(stmt);
    }
  }

  void VisitCompoundAssignOperator(CompoundAssignOperator *cao) {
    llvm::outs() << "(CompoundAssignOperator " << cao->getOpcodeStr().data()
                 << ' ';
    RECURSE_CHILDREN_STMT(cao);
    llvm::outs() << ')';
  }

  void VisitMemberExpr(MemberExpr *me) {
    llvm::outs() << "(MemberExpr ";
    RECURSE_CHILDREN_STMT(me);
    llvm::outs() << me->getMemberDecl()->getNameAsString() << ')';
  }

  void VisitDeclStmt(DeclStmt *stmt) {
    if (stmt->isSingleDecl()) {
      llvm::outs() << "(DeclStmt ";
      if (auto *var = dyn_cast<VarDecl>(stmt->getSingleDecl()))
        DispatchDecl(var);
      else
        llvm::outs() << stmt->getSingleDecl()->getDeclKindName();

      llvm::outs() << ')';
    }
  }

  void VisitIntegerLiteral(IntegerLiteral *i) {
    llvm::outs() << "(IntegerLiteral " << i->getValue().getLimitedValue()
                 << ' ';
    printType(i->getType());
    llvm::outs() << ")";
  }

  void VisitStringLiteral(StringLiteral *s) {
    llvm::outs() << "(StringLiteral ";
    s->outputString(llvm::outs());
    llvm::outs() << ")";
  }

  void VisitDeclRefExpr(DeclRefExpr *ref) {
    llvm::outs() << '(' << ref->getDecl()->getNameAsString() << ')';
  }

  void VisitUnaryOperator(UnaryOperator *op) {
    llvm::outs() << "(UnaryOperator "
                 << UnaryOperator::getOpcodeStr(op->getOpcode()).data() << ' ';
    DispatchStmt(op->getSubExpr());
    llvm::outs() << ')';
  }

  void VisitBinaryOperator(BinaryOperator *op) {
    llvm::outs() << "(BinaryOperator " << op->getOpcodeStr().data() << ' ';

    DispatchStmt(op->getLHS());
    DispatchStmt(op->getRHS());

    llvm::outs() << ')';
  }

  void VisitStmt(Stmt *stmt) {
    llvm::outs() << '(' << stmt->getStmtClassName();

    RECURSE_CHILDREN_STMT(stmt);

    llvm::outs() << ')';
  }

  void setSourceManager(SourceManager *SM) { _sourceManager = SM; }

private:
  SourceManager *_sourceManager;
};

class SexpConsumer : public ASTConsumer {
public:
  virtual void HandleTranslationUnit(ASTContext &Context) {
    _visitor.setSourceManager(&Context.getSourceManager());
    llvm::outs() << "(TranslationUnit \"" << _file << "\" ";
    _visitor.VisitTranslationUnit(Context.getTranslationUnitDecl());
    llvm::outs() << ')';
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

static llvm::cl::OptionCategory ClangSexpCategory("clang-sexpression options");

static llvm::cl::extrahelp CommonHelp(CommonOptionsParser::HelpMessage);

static llvm::cl::extrahelp
    MoreHelp("\nThis tool converts clang ASTs to S-Expressions\n");

int main(int argc, const char **argv) {
  CommonOptionsParser OptionsParser(argc, argv, ClangSexpCategory);
  auto compilationDatabaseFiles = OptionsParser.getCompilations().getAllFiles();
  auto &files = OptionsParser.getSourcePathList();

  ClangTool Tool(OptionsParser.getCompilations(), compilationDatabaseFiles);
  llvm::outs() << "(ROOT ";
  auto ret = Tool.run(newFrontendActionFactory<SexpAction>().get());
  llvm::outs() << ')';

  return ret;
}
