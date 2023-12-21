import Swift
public struct AnyDifferentiable: Differentiable {
  let x: Int 

  @differentiable(reverse)
  public init<T: Differentiable>(_ base: T) {
    self.x = 42
  }
}

public struct AnyDerivative2 {
  let x: Int = 0

  public init() {}
  
  @inlinable
  public static func sub (
    lhs: AnyDerivative2, rhs: AnyDerivative2
  ) -> AnyDerivative2 {
    return AnyDerivative2()
  }

  @derivative(of: sub)
  internal static func subDerive(
    lhs: AnyDerivative2, rhs: AnyDerivative2
  ) -> (
    value: AnyDerivative2,
    pullback: (AnyDerivative2) -> (AnyDerivative2, AnyDerivative2)
  ) {
    return (lhs, { v in (v,v) })
  }
} 