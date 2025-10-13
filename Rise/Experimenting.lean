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

-- #eval runSygus  "
--   (set-logic NIA)
--   (synth-fun p ((q Int)) Int)
--   (declare-var q Int)
--   (assume (> q 0))
--   (constraint (> (p q) 0))
--   (assume (= ((p q)) (div q 4))
--   (check-synth)
-- "


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



#eval runSygus "
(set-logic ALL)

(declare-var b Int)
(synth-fun m ((b Int)) Int)

(assume (> b 0))
(constraint (> (m b) 0))
(assume (exists ((mp Int)) (= (* mp 4) b)))

(constraint (= (* (m b) 4) b))

(check-synth)

"

#eval runSygus "

(set-logic NIA)

(synth-fun sideCondition ((n Int)) Bool
  ((B Bool) (I Int))
  ((B Bool (true false
              (= I I)
              (< I I)
              (and B B)
              (or B B)
              (not B)))
   (I Int (n 0 1 2 3 4 (+ I I) (- I I) (* I I) (mod I I)))))

(constraint (sideCondition 4))
(constraint (sideCondition 8))
(constraint (exists ((n Int)) (and (> n 0) (sideCondition n))))

; ∀n . (n>0 )
(constraint (forall ((n Int))
  (=> (and (> n 0) (sideCondition n))
      (exists ((m Int))
        (and (> m 0)
             (= m (div n 4))
             (= n (* 4 m)))))))

(check-synth)
  
"
#eval runSygus "

(set-logic NIA)

(synth-fun sideCondition ((n Int)) Bool
  ((B Bool) (I Int))
  ((B Bool ((= I 0) (> n I)))
   (I Int (n 4 (mod n I)))))

; ∃n.(n>0 ∧ sideCondition(n))
; i.e., n>0 must exist
(constraint (exists ((n Int)) (and (> n 0) (sideCondition n))))

; ∀n.((n>0 ∧ sideCondition(n)) ⇒ ∃m.(m>0 ∧ m = n/4 ∧ n = 4*m))
(constraint (forall ((n Int))
  (=> (and (> n 0) (sideCondition n))
      (exists ((m Int))
        (and (> m 0)
             (= m (div n 4))
             (= n (* 4 m)))))))

(check-synth)
  
"

#eval runSygus "

(set-logic NIA)

(synth-fun sideCondition ((n Int)) Bool
  ((B Bool) (I Int))
  ((B Bool ((= I 0) (> n I)))
   (I Int (n 0 4 (mod I I)))))

;(constraint (sideCondition 4))
;(constraint (sideCondition 8))
(constraint (exists ((n Int)) (and (> n 0) (sideCondition n))))

; ∀n.((n>0 ∧ sideCondition n) ⇒ ∃m.(m>0 ∧ m = n/4 ∧ n = 4*m))
(constraint (forall ((n Int))
  (=> (and (> n 0) (sideCondition n))
      (exists ((m Int))
        (and (> m 0)
             (= m (- n 4))
             (= n (+ m 4)))))))

(check-synth)
  
"

#eval runSygus "
    (set-logic NRA)
    (synth-fun m?30 ((n.1 Real)) Real)
    ;(synth-fun n?30 ((n.1 Real)) Real)
    (declare-var n.1 Real)
    ;todo
    (constraint (> n.1 0))
    (constraint (> (m?30 n.1) 0))
    (constraint (= (* (m?30 n.1) (m?30 n.1)) n.1))
    (check-synth)
    
"
#eval runSygus "
    (set-logic NRA)
    (synth-fun m?30 ((n.1 Real) (n?30 Real)) Real)
    (declare-var n1 Real)
    (declare-var n.1 Real)
    ;todo
    ;(constraint (> n.1 0))
    (constraint (= (* (m?30 n.1) (n?30 n.1)) n.1))
    (check-synth)
    
"
