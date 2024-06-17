// RUN: %target-typecheck-verify-swift -verify-ignore-unknown -I %S/Inputs -cxx-interoperability-mode=default
// RUN: %target-typecheck-verify-swift -verify-ignore-unknown -I %S/Inputs

import CustomStringBuiltins

public func testMemcpyOptionalReturn(p: UnsafeMutableRawPointer, e: UnsafeRawPointer) {
  // This 'memcpy' is a builtin and is always an optional, regardless of _Nonnull.
  let x = CustomStringBuiltins.memcpy(p, e, 1)!

  // Not a builtin, _Nonnull makes it a non-optional.
  let y = CustomStringBuiltins.memcpy42(p, e, 1)! // expected-error {{cannot force unwrap value of non-optional type 'UnsafeMutableRawPointer'}}
}