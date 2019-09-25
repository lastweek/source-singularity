; -------------------------------------------------------------------------
; Boogie universal background predicate
; Copyright (c), Microsoft Corp.
  :category { industrial }

  ; select/store axioms, 1 index argument
  :assumption
  (forall (?a Any) (?i Any) (?v Any)
    (= (select1 (store1 ?a ?i ?v) ?i) ?v))

  :assumption
  (forall (?a Any) (?i Any) (?j Any) (?v Any)
    (implies (!= ?i ?j)
      (=
        (select1 (store1 ?a ?i ?v) ?j)
        (select1 ?a ?j))))

  ; select/store axioms, 2 index arguments
  :assumption
  (forall (?a Any) (?o Any) (?f Any) (?v Any)
    (= (select2 (store2 ?a ?o ?f ?v) ?o ?f) ?v))

  :assumption
  (forall (?a Any) (?o Any) (?f Any) (?p Any) (?g Any) (?v Any)
    (implies (!= ?o ?p)
      (=
        (select2 (store2 ?a ?o ?f ?v) ?p ?g)
        (select2 ?a ?p ?g))))

  :assumption
  (forall (?a Any) (?o Any) (?f Any) (?p Any) (?g Any) (?v Any)
    (implies (!= ?f ?g)
      (=
        (select2 (store2 ?a ?o ?f ?v) ?p ?g)
        (select2 ?a ?p ?g))))

  ; formula/term axioms
  :assumption
  (forall (?x Any) (?y Any)
    (iff
      (= (boolIff ?x ?y) boolTrue)
      (iff (= ?x boolTrue) (= ?y boolTrue))))

  :assumption
  (forall (?x Any) (?y Any)
    (iff
      (= (boolImplies ?x ?y) boolTrue)
      (implies (= ?x boolTrue) (= ?y boolTrue))))

  :assumption
  (forall (?x Any) (?y Any)
    (iff
      (= (boolAnd ?x ?y) boolTrue)
      (and (= ?x boolTrue) (= ?y boolTrue))))

  :assumption
  (forall (?x Any) (?y Any)
    (iff
      (= (boolOr ?x ?y) boolTrue)
      (or (= ?x boolTrue) (= ?y boolTrue))))

  :assumption
  (forall (?x Any)
    (iff
      (= (boolNot ?x) boolTrue)
      (!= ?x boolTrue))
    :pat { (boolNot ?x) }
  )

  :assumption
  (forall (?x Any) (?y Any)
    (iff
      (= (anyEqual ?x ?y) boolTrue)
      (= ?x ?y)))

  :assumption
  (forall (?x Any) (?y Any)
    (iff
      (= (anyNeq ?x ?y) boolTrue)
      (!= ?x ?y))
    :pat  { (anyNeq ?x ?y) }
  )

  :assumption
  (forall (?x Any) (?y Any)
    (iff
      (= (intLess ?x ?y) boolTrue)
      (< ?x ?y)))

  :assumption
  (forall (?x Any) (?y Any)
    (iff
      (= (intAtMost ?x ?y) boolTrue)
      (<= ?x ?y)))

  :assumption
  (forall (?x Any) (?y Any)
    (iff
      (= (intAtLeast ?x ?y) boolTrue)
      (>= ?x ?y)))

  :assumption
  (forall (?x Any) (?y Any)
    (iff
      (= (intGreater ?x ?y) boolTrue)
      (> ?x ?y)))

  ; false is not true
  :assumption
  (distinct boolFalse boolTrue)

  ; <: is a partial order:  it is reflexive, transitive, and anti-symmetric
  ; x'''60_'58_ is the encoding we use

  :assumption
  (forall (?t Any)
    (x'''60_'58_ ?t ?t)
    :pat { (x'''60_'58_ ?t ?t) }
  )

  :assumption
  (forall (?t Any) (?u Any) (?v Any)
    (implies
      (and (x'''60_'58_ ?t ?u) (x'''60_'58_ ?u ?v))
      (x'''60_'58_ ?t ?v))
    :pat { (x'''60_'58_ ?t ?u) (x'''60_'58_ ?u ?v) }
  )

  :assumption
  (forall (?t Any) (?u Any)
    (implies
      (and (x'''60_'58_ ?t ?u) (x'''60_'58_ ?u ?t))
      (= ?t ?u))
    :pat { (x'''60_'58_ ?t ?u) (x'''60_'58_ ?u ?t) }
  )

; End Boogie universal background predicate
; -------------------------------------------------------------------------

