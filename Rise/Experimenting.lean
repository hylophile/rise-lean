import Rise.Solve


#eval runSygus  "
  (set-logic NRA)
  (synth-fun p ((q Real)) Real)
  (declare-var q Real)
  (assume (> q 0))
  (constraint (> (p q) 0))
  (constraint (= (* (p q) 4) q))
  (check-synth)
"

#eval runSygus  "
  (set-logic NIA)
  (declare-fun p ((q Int)) Int)
  (declare-var q Int)
  (synth-fun b () Bool)
  (assume (> q 0))
  (constraint (> (p q) 0))
  (constraint (=>
    (and
      b
      (= (p q) (div q 4)))
    (>= (p q) 0)))
  (check-synth)
"

#eval runSygus "

(set-logic NIA)

(synth-fun sidecond ((x Int)) Bool
  ((B Bool) (R Int))
  (
    (B Bool ((= (mod R R) 0)
            ; (< R R) (<= R R) (>= R R) (= R R)
            ; (and B B) (not B)
            ))
    (R Int (x 4))
  )
)

(declare-var x Int)

(constraint (=> (and (sidecond x))
                (> (div x 4) 0)))

(check-synth)

  
"

