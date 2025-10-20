import Rise.Program
-- src/main/scala/apps/localLaplacian.scala 

-- src/main/scala/rise/core/DSL/HighLevelConstructs.scala 
def padClamp2D := [RiseC|
  fun lOuter rOuter lInner rInner : nat =>
  map (padClamp (lInner : nat) (rInner : nat)) >> padClamp (lOuter : nat) (rOuter : nat)
]
#pp padClamp2D.type


def prodMult := [RiseC| fun {d : data} => fun xs : d × d => xs.1 * xs.2]
-- #pp prodMult.type

def dot := [RiseC|
  fun {n : nat} =>
  fun as bs : n·f32 =>
     zip as bs |> map $prodMult |> reduce add 0.0f32
]
-- #pp dot.type

-- /**
--   * Division operator in Natural set (ie int div like Scala): `1/2=0`.
--   *
--   * @param that Right-hand side (divisor).
--   * @return An IntDiv object wrapping the operands.
--   * @throws ArithmeticException if the right-hand-side is zero.
--   */
-- def /(that: ArithExpr): ArithExpr with SimplifiedExpr = ExprSimplifier.fixpoint(IntDiv(this, that))

-- /**
--   * Ordinal division operator.
--   * This prevents integer arithmetic simplification through exponentiation.
--   *
--   * @param that Right-hand side (divisor).
--   * @return The expression multiplied by the divisor exponent -1.
--   */
-- def /^(that: ArithExpr): ArithExpr with SimplifiedExpr = this * that.pow(-1)


-- (1 : nat) (2 + 2*(1 + h/2 - h/^2) : nat) -- 1 - h % 2
-- (1 : nat) (2 + 2*(1 + w/2 - w/^2) : nat) -- 1 - w % 2
-- it seems the comments here are wrong and should be "2*(1 + h/2 - h/^2) = 2 - h % 2" ?
-- 2*(5/2 - 5/^2)
-- 2*(1+2  -5/^2)
-- 2*(3  -5/^2)
-- 2*3  - 2*5/^2
-- 6  - 5
-- 1
--
-- 2*(1+6/2-6/^2)
-- 2*(1+3-6/^2)
-- 2*(4-6/^2)
-- 8-6
-- 2
-- 
def downSample2D := [RiseC|
  def downSampleWeights : 4·f32

  fun h w : nat =>
  fun input : h+3·w+3·f32 =>
  input |>
  $padClamp2D 
      (1 : nat) (2 + 2*(1 + h/2 - h/2) : nat) -- 1 - h % 2
      (1 : nat) (2 + 2*(1 + w/2 - w/2) : nat) -- 1 - w % 2
  >> map (slide (4 : nat) (2 : nat))
  >> slide (4 : nat) (2 : nat)
  >> map transpose
  >> map (map (map ($dot downSampleWeights) >> $dot downSampleWeights))


]
#pp downSample2D.type
