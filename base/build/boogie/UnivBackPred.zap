; ----------------------------------------------------------------------
; Boogie universal background predicate
; Copyright (c), Microsoft Corp.
(&&
  ; select/store axioms, 1 index argument

  (forall (A i v)
    (= (select1 (store1 A i v) i) v))

  (forall (A i j v)
    (==> (!= i j)
      (=
        (select1 (store1 A i v) j)
        (select1 A j))))

  ; select/store axioms, 2 index arguments

  (forall (A o f v)
    (= (select2 (store2 A o f v) o f) v))

  (forall (A o f p g v)
    (==> (!= o p)
      (=
        (select2 (store2 A o f v) p g)
        (select2 A p g))))

  (forall (A o f p g v)
    (==> (!= f g)
      (=
        (select2 (store2 A o f v) p g)
        (select2 A p g))))

  ; <: is a partial order:  it is reflexive, transitive, and anti-symmetric

  (forall (t)
    (<: t t)
    (PATS (<: t t)))

  (forall (t u v)
    (==>
      (&& (<: t u ) (<: u v))
      (<: t v))
    (PATS (MPAT (= (<: t u) true) (= (<: u v) true))))

  (forall (t u)
    (==>
      (&& (<: t u) (<: u t))
      (= t u))
    (PATS (MPAT (<: t u) (<: u t))))

)
; End Boogie universal background predicate
; ----------------------------------------------------------------------
