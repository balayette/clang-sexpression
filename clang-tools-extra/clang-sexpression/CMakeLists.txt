set(LLVM_LINK_COMPONENTS support)

add_clang_executable(clang-sexpression
	ClangSexpression.cpp
)

target_link_libraries(clang-sexpression
  PRIVATE
  clangAST
  clangFrontend
  clangTooling
)

