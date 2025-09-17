set(LLVM_TARGET_DEFINITIONS ${CMAKE_CURRENT_SOURCE_DIR}/../include/Koka/KokaDialect.td)
mlir_tablegen(KokaDialect.h.inc -gen-dialect-decls -dialect=koka)
mlir_tablegen(KokaDialect.cpp.inc -gen-dialect-defs -dialect=koka)
add_public_tablegen_target(KokaIncGen)

add_mlir_dialect(Koka koka)
add_mlir_doc(KokaDialect KokaDialect dialects/ -gen-dialect-doc)