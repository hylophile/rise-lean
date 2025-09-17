#check [RiseT| {n : nat} → {s : data} → {t : data} → n·(s × t) → (n·s × n·t)]
#check [RiseT| {n m p q : nat} → {t : data} → n+m*q*p·t]

#eval [RiseT| {n m p q : nat} → {t : data} → n-m-p·t].toString
#eval [RiseT| {n m p q : nat} → {t : data} → n-m+p·t].toString
#eval [RiseT| {n m p q : nat} → {t : data} → n-m*p·t].toString
#eval [RiseT| {n m p q : nat} → {t : data} → n-m*p+q·t].toString
#eval [RiseT| {n m p q : nat} → {t : data} → n-m*p^q·t].toString


#check [RiseT| (n t : data) → n·t → n·t × n·t]

-- #check [RiseT| {n t : data} → n·t → n·t × n·t]
#check [RiseT| f32]
#check [RiseT| f64 → f64 ]
#check [RiseT| {δ : data} → δ → δ → δ]
#check [RiseT| {δ1 δ2 : data} → δ1 × δ2 → δ1]
#guard [RiseT| {δ1 δ2 : data} → δ1 × δ2 → δ1] ==
  RType.pi RKind.data RBinderInfo.implicit `δ1
        (RType.pi RKind.data RBinderInfo.implicit `δ2
          ((RType.data ((RData.bvar 1 `δ1).pair (RData.bvar 0 `δ2))).fn (RType.data (RData.bvar 1 `δ1))))


#check [RiseT| {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n·δ1 → n·δ2]

