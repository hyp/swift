// RUN: %target-run-simple-swift(-I %S/Inputs/ -Xfrontend -enable-experimental-cxx-interop)
//
// REQUIRES: executable_test

import MoveOnlyCxxOperators
import StdlibUnittest

var MoveOnlyCxxSubscripts = TestSuite("Move Only Subscripts")

func borrowNC(_ x: borrowing NonCopyable) -> CInt {
  return x.method(3)
}

func inoutNC(_ x: inout NonCopyable, _ y: CInt) -> CInt {
  return x.mutMethod(y)
}

func consumingNC(_ x: consuming NonCopyable) {
  // do nothing.
}


MoveOnlyCxxSubscripts.test("NonCopyableHolderConstSubscript subscript borrow") {
  let holder = NonCopyableHolderConstSubscript(-9, 7)
  var k = borrowNC(holder[0])
  expectEqual(k, -27)
  /*k = holder[1].method(2)
  expectEqual(k, 14)
  k = holder[0].x
  expectEqual(k, 7)*/
}

/*
MoveOnlyCxxSubscripts.test("testNonCopyableHolderPairedDeref pointee borrow") {
  var holder = NonCopyableHolderPairedDeref(11)
  var k = borrowNC(holder.pointee)
  expectEqual(k, 33)
  k = holder.pointee.method(2)
  expectEqual(k, 22)
  k = holder.pointee.x
  expectEqual(k, 11)
  k = inoutNC(&holder.pointee, -1)
  expectEqual(k, -1)
  expectEqual(holder.pointee.x, -1)
  holder.pointee.mutMethod(3)
  expectEqual(holder.pointee.x, 3)
  holder.pointee.x = 34
  expectEqual(holder.pointee.x, 34)
  consumingNC(holder.pointee)
  expectEqual(holder.pointee.x, 0)
}

 MoveOnlyCxxSubscripts.test("testNonCopyableHolderMutDeref pointee borrow") {
  var holder = NonCopyableHolderMutDeref(11)
  var k = borrowNC(holder.pointee)
  expectEqual(k, 33)
  k = holder.pointee.method(2)
  expectEqual(k, 22)
  k = holder.pointee.x
  expectEqual(k, 11)
  k = inoutNC(&holder.pointee, -1)
  expectEqual(k, -1)
  expectEqual(holder.pointee.x, -1)
  holder.pointee.mutMethod(3)
  expectEqual(holder.pointee.x, 3)
  holder.pointee.x = 34
  expectEqual(holder.pointee.x, 34)
  consumingNC(holder.pointee)
  expectEqual(holder.pointee.x, 0)
}

 MoveOnlyCxxSubscripts.test("testNonCopyableHolderValueConstDeref pointee value") {
  let holder = NonCopyableHolderValueConstDeref(11)
  var k = holder.pointee
  var k2 = holder.pointee
  expectEqual(k.x, k2.x)
}

 MoveOnlyCxxSubscripts.test("testNonCopyableHolderValueMutDeref pointee value") {
  var holder = NonCopyableHolderValueMutDeref(11)
  var k = holder.pointee
  var k2 = holder.pointee
  expectE
 qual(k.x, k2.x)
}*/

runAllTests()
