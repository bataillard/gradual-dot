#lang racket

(require redex
         redex/tut-subst)
(provide (all-defined-out))

;; ===========================

;; DOT Syntax

;; ===========================
(define-language DOT
  
  (v ::= (ν (x : T) d)
         (λ (x : T) t))
  
  (t ::= x
         v
         (x x)
         (x sel a)
         (let x = t in t))

  (d ::= {A = T}
         {a = t}
         (d ∧ d))   ; TODO How to specify associativity and commutativity of ∧?
  
  (a ::= (mem x))
  
  (A ::= (tmem x))
  
  (T ::= ⊤
         ⊥
         {A : T .. T}
         {a : T}
         (T ∧ T)    ; TODO How to specify associativity and commutativity of ∧?
         (μ (x : T))
         (x sel A)
         (∀ (x: T) T))
  
  (E ::= hole
         (let x = hole in t)
         (let x = v in E))
  
  (Γ ::= ·
         (Γ (x : T)))
  
  (x ::= variable-not-otherwise-mentioned))

;; ===========================

;; DOT Type system

;; ===========================


; Metafunctions taken from marianna rapoport's github stub:
; https://github.com/amaurremi/dot-plt-redex/blob/master/dot_old.rkt

(define-metafunction DOT
  fv : T -> (x ...)
  [(fv ⊤) ()] 
  [(fv ⊥) ()]
  [(fv {A : T_1 .. T_2}) (append (fv T_1) (fv T_2))]
  [(fv (x sel A)) (x)]
  [(fv (∀ (x: T_1) T_2)) (subtract (append (fv T_1) (fv T_2)) x)])

(define-metafunction DOT
  append : (any ...) (any ...) -> (any ...)
  [(append (any_1 ...) (any_2 ...)) (any_1 ... any_2 ...)])

(define-metafunction DOT
  subtract : (x ...) x ... -> (x ...)
  [(subtract (x ...)) (x ...)]
  [(subtract (x ...) x_1 x_2 ...)
   (subtract (subtract1 (x ...) x_1) x_2 ...)])

(define-metafunction DOT
  disjoint : any ... -> boolean
  [(disjoint any_!_1 ...) #t]
  [(disjoint _ ...) #f])

(define-metafunction DOT
  dom : d d -> (any ...)
  [(dom {a = _}) (a)]
  [(dom {A = _}) (A)]
  [(dom {d_1 ∧ d_2}) (append (dom d_1) (dom d_2))])

(define (not-in-fv x U)
  (not (member (term x) (term (fv U)))))

;; TODO Introduce replacement rules for subsumption

;; TODO in many rules, the mode is not I I O, so plt redex considers variables unbound
;; and throws an error (such as in Top and Bottom)

; Subtyping for terms
(define-judgment-form DOT
  ; #:mode (<: I I O)
  ; OR SOMETIMES
  ; #:mode (<: I O I)
  ; OR SOMETIMES
  ; #:mode (<: I I I)
  #:contract (<: Г T T)

  [----------- "Top"
   (<: Г T ⊤)]
 
  [----------- "Bot"
   (<: Г ⊥ T)]
  
  [----------- "Refl"
   (<: Г T T)]

  [(<: Г T_1 T_2)
   (<: Г T_2 T_3)
   -------------- "Trans"
   (<: Г T_1 T_3)]

  [(⊢ Г x_0 : {A : T_low .. T_high})
   --------------------------------- "<:-Sel"
   (<: Г T_low (x_0 sel A))]

  [(⊢ Г x_0 : {A : T_low .. T_high})
   --------------------------------- "Sel-<:"
   (<: Г (x_0 sel A) T_high)]

  [(<: Г T_arg2 T_arg1)
   (<: (Г (x_0 : T_arg2)) T_body1 T_body2)
   ---------------------------------------------------------- "All-<:-All"
   (<: Г (∀ (x_0: T_arg1) T_body1) (∀ (x_0: T_arg2) T_body2))]

  [(<: Г T_low2 T_low1)
   (<: Г T_high1 T_high2)
   --------------------------------------------------- "Typ-<:-Typ"
   (<: Г {A : T_low1 .. T_high1} {A : T_low2 T_high2})]

  [---------------------- "And_1-<:"
   (<: Г (T_1 ∧ T_2) T_1)]

  [---------------------- "And_2-<:"
   (<: Г (T_1 ∧ T_2) T_2)]

  [(<: Г T_1 T_2)
   -------------------------- "Fld-<:-Fld"
   (<: Г {a = T_1} {a = T_2})]

  [(<: Г T_0 T_1)
   (<: Г T_0 T_2)
   ---------------------- "<:-And"
   (<: Г T_0 (T_1 ∧ T_2))])

; Type assignment for terms
(define-judgment-form DOT
  #:mode (⊢ I I I O) 
  #:contract (⊢ Γ t : T)

  [-------------------- "Var"
   (⊢ (Γ (x : A)) x : A)]

  [(⊢ (Γ (x : T_arg)) t : T_body)
   (side-condition (not-in-fv x T_arg))
   ------------------------------------------------- "All-I"
   (⊢ Γ (λ (x : T_arg) t) : (∀ (x : T_arg) T_body))]

  [(⊢ Γ t_1 : T_1)
   (⊢ (Γ (x : T_1)) t_2 : T_2)
   (side-condition (not-in-fv x T_2))
   ------------------------------------ "Let"
   (⊢ Γ (let x = t_1 in t_2) : T_2)]

  [(⊢ Γ x_func : (∀ (x_param : T_param) T_body))
   (⊢ Γ x_arg : T_arg)
   -------------------------------------------------------- "All-E"
   (⊢ Γ (x_func x_arg) : (type-subst x_param x_arg T_body))]

  [(⊢d (Γ (x : T)) d : T)
   --------------------------------- "{}-I"
   (⊢ Γ (ν (x : T) d) : (μ (x : T)))]

  [(⊢ Γ x : {a : T})
   ------------------- "Fld-E"
   (⊢ Γ (x sel a) : T)]

  [(⊢ Γ x : T)
   -------------------- "Rec-I"
   (⊢ Γ x : (μ (x : T)))]
  ; TODO Rec-E and Rec-I will probably cause infinite loops

  [(⊢ Γ x : (μ (x : T)))
   -------------------- "Rec-E"
   (⊢ Γ x : T)]

  [(⊢ Γ x : T_1)
   (⊢ Γ x : T_2)
   ---------------------- "And-I"
   (⊢ Γ x : (T_1 ∧ T_2))]


  ;; TODO Find better way to do this if necessary 
  ;; ======== Custom conjunction associativity solution =======
  [(⊢ Γ t : (T_1 ∧ T_2))
   ---------------------- "Typ-Sym"
   (⊢ Γ t : (T_2 ∧ T_1))]
  
  [(⊢ Γ t : (T_1 ∧ (T_2 ∧ T_3)))
   ----------------------------- "Typ-Assoc-RL"
   (⊢ Γ t : ((T_1 ∧ T_2) ∧ T_3))]

  [(⊢ Γ t : ((T_1 ∧ T_2) ∧ T_3))
   ----------------------------- "Typ-Assoc-LR"
   (⊢ Γ t : (T_1 ∧ (T_2 ∧ T_3)))])

; Subtyping for members
(define-judgment-form DOT
  #:mode (⊢d I I I O)
  #:contract (⊢d Γ d : T)

  [------------------------------------ "Typ-I"
   (⊢d Γ {A = T_0} : {A : T_0 .. T_0})]

  [(⊢ Γ t : T)
   ----------------------------- "Fld-I"
   (⊢d Γ {a_0 = t} : {a_0 : T})]

  [(⊢d Γ d_1 : T_1)
   (⊢d Γ d_2 : T_2)
   (side-condition (disjoint (append (dom d_1) (dom d_2))))
   -------------------------------------------------------- "AndDef-I"
   (⊢d Γ (d_1 ∧ d_2) : (T_1 ∧ T_2))]

  ;; TODO Find better way to do this necessary 
  ;; ======== Custom conjunction associativity solution =======
  [(⊢d Γ d : (T_1 ∧ T_2))
   ---------------------- "Mem-Sym"
   (⊢d Γ d : (T_2 ∧ T_1))]
  
  [(⊢d Γ d : (T_1 ∧ (T_2 ∧ T_3)))
   ----------------------------- "Mem-Assoc-RL"
   (⊢d Γ d : ((T_1 ∧ T_2) ∧ T_3))]

  [(⊢d Γ d : ((T_1 ∧ T_2) ∧ T_3))
   ----------------------------- "Mem-Assoc-LR"
   (⊢d Γ d : (T_1 ∧ (T_2 ∧ T_3)))])

;; ===========================
;;
;; Evaluation Semantics
;;
;; ===========================

;; Substitution function for DOT
(define-metafunction DOT
  subst : x x t -> t
  [(subst x y t)
   ,(subst/proc x? (list (term x)) (list (term y)) (term t))])

(define-metafunction DOT
  type-subst : x x T -> T
  [(type-subst x y t)
   ,(subst/proc x? (list (term x)) (list (term y)) (term T))])

(define x? (redex-match DOT x))

(define T? (redex-match DOT T))

;; Reduction step for evaluation
(define ↝
  (reduction-relation
   DOT
   #:domain t

   (--> (let x_1 = x_2 in t_1)
        (subst x_1 x_2 t_1))

   (--> (let x_1 = (let x_2 = t_1 in t_2) in t_3)
        (let x_2 = t_1 in (let x_1 = t_2 in t_3)))
   
   (--> (let x_func = (λ (x_param : T) t) in (in-hole E (x_func x_arg)))
        (let x_func = (λ (x_param : T) t) in (in-hole E (subst x_param x_arg t))))

   (--> (let x_obj = (ν (x : T) d_1 ... { a_mem = t } d_2 ...)
          in (in-hole E (x_obj sel a_mem)))
        (let x_obj = (ν (x : T) d_1 ... { a_mem = t } d_2 ...)
          in (in-hole E t)))))

(define -->E
  (context-closure ↝ DOT E))

;; Unit tests for evaluation
(test-->>
 -->E
 (term
  (let x = (λ (a : ⊤) a)
    in x))
 (term (let x = (λ (a : ⊤) a)
    in x)))

(test-->>
 -->E
 (term
  (let x = (λ (a : ⊤) a) in
    (let y = (λ (a : ⊤) a) in
      (x y))))
 (term
  (let x = (λ (a : ⊤) a) in
    (let y = (λ (a : ⊤) a) in
      y))))

(test-->>
 -->E
 (term
  (let x = (let y = (λ (a : ⊤) a)
             in y)
    in x))
 (term
  (let y = (λ (a : ⊤) a)
    in y)))

(test-->>
 -->E
 (term
  (let x = (ν (self : ⊤)
              {(mem a) = (λ (x : ⊤) x)}
              {(mem b) = (λ (y : ⊤) y)}
              {(mem c) = (λ (z : ⊤) z)})
    in (x sel (mem b))))
  (term
  (let x = (ν (self : ⊤)
              {(mem a) = (λ (x : ⊤) x)}
              {(mem b) = (λ (y : ⊤) y)}
              {(mem c) = (λ (z : ⊤) z)})
    in (λ (y : ⊤) y))))

 
          
  

