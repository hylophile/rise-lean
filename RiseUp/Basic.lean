import Lean

declare_syntax_cat                                                rise_expr
syntax     ident                                                : rise_expr
syntax     num                                                  : rise_expr
syntax     scientific                                           : rise_expr
syntax     "fun" "(" ident+ (":" rise_expr)? ")" "=>" rise_expr : rise_expr
syntax     "fun"     ident+ (":" rise_expr)?     "=>" rise_expr : rise_expr
syntax     "fun" "(" ident+ (":" rise_expr)  ")" "=>" rise_expr : rise_expr
syntax     "fun" "{" ident+ (":" rise_expr)  "}" "=>" rise_expr : rise_expr
syntax     "fun"     ident+ ":" rise_expr        "=>" rise_expr : rise_expr
syntax     "let" ident ":=" rise_expr "in" rise_expr            : rise_expr
syntax:10  rise_expr:10 "+" rise_expr:11                        : rise_expr
syntax:10  rise_expr:10 "-" rise_expr:11                        : rise_expr
syntax:20  rise_expr:20 "*" rise_expr:21                        : rise_expr
syntax:20  rise_expr:20 "/" rise_expr:21                        : rise_expr
syntax:30  rise_expr    "^" rise_expr                           : rise_expr
syntax     rise_expr ".1"                                       : rise_expr
syntax     rise_expr ".2"                                       : rise_expr
syntax     "true"                                               : rise_expr
syntax     "false"                                              : rise_expr
syntax     "type"                                               : rise_expr
syntax     "kind"                                               : rise_expr
syntax:50  rise_expr:50 rise_expr:51                            : rise_expr
syntax:40  rise_expr:40 "|>" rise_expr:41                       : rise_expr
syntax:40  rise_expr:40 "<|" rise_expr:41                       : rise_expr
syntax:41  rise_expr:41 ">>" rise_expr:42                       : rise_expr
syntax:41  rise_expr:41 "<<" rise_expr:42                       : rise_expr
syntax     "(" rise_expr ")"                                    : rise_expr
syntax     "(" rise_expr ":" rise_expr ")"                      : rise_expr

syntax:min rise_expr "→" rise_expr                              : rise_expr
syntax     "{" ident+ ":" rise_expr "}" "→" rise_expr           : rise_expr
syntax     "(" ident+ ":" rise_expr ")" "→" rise_expr           : rise_expr
syntax:80  rise_expr:81 "·" rise_expr:80                        : rise_expr
syntax:10  rise_expr "×" rise_expr                              : rise_expr
syntax     "idx[" rise_expr "]"                                 : rise_expr
syntax     rise_expr "<" rise_expr ">"                          : rise_expr

declare_syntax_cat                                                rise_def
syntax     "def" ident ":" rise_expr ";"                        : rise_def

declare_syntax_cat                                                rise_import
syntax     "import" ident ";"                                   : rise_import

declare_syntax_cat                                                rise_program
syntax     (rise_import)* (rise_def)* linebreak rise_expr       : rise_program

syntax "[R|" rise_program "]" : term

elab "[R|" p:rise_program "]" : term => do
  dbg_trace p
  pure (Lean.Expr.lit (.natVal 1))

#check [R|
import core;
def map : {n : nat} → {s t : data} → (s → t) → n·s → n·t;
map (asc : a → b) xs
]


#check [R|
  def upsampleWeights1 : 2·f32;
  def upsampleWeights2 : 2·f32;
  def lidx : (i n : nat) → idx[n];

  fun h w : nat =>
  fun input : (h/2)+3·(w/2)+3·f32 =>
  input |>
  padClamp2D 1 0
             1 0
  >> slide2D 2 1
  >> map (map (fun nbh =>
      generate (fun yi : idx[2] =>
          generate (fun xi : idx[2] =>
            let wy := (select (equal xi <| lidx 0 2) upsampleWeights1 upsampleWeights2) in
            let wx := (select (equal yi <| lidx 0 2) upsampleWeights1 upsampleWeights2) in
            nbh
            |> map (dot wx)
               >> dot wy
          ))))
  >> map (transpose >> map join)
  >> join
  >> drop 1
  >> dropLast (2 + 2*(h/2) - h)
  >> map (drop 1 >> dropLast (2 + 2*(w/2) - w))
]

-- elab "[T|" t:term "]" : term => do
--   dbg_trace t
--   pure (Lean.Expr.lit (.natVal 1))

-- #check [T|
-- -- import core
-- def map : {n : nat} → {s t : data} → (s → t) → n·s → n·t
-- map f xs
-- ]
