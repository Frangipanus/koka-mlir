#ifndef KOKA_DIALECT
#define KOKA_DIALECT

include "mlir/IR/Dialect.h.td"

def Koka_Dialect : Dialect {
  let name = "koka";
  let cppNamespace = "::koka";
}

#endif // KOKA_DIALECT