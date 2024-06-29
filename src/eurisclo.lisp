;; Dribble files:
;;  RLL.DRI[AM,DBL]
;;  TRACE.MA2[AM,DBL]
;;  TRACE.MA2[AM,DBL]1
;;  TRACE.MAR[AM,DBL]
;;  TR324.6[AM,DBL]
;;  T329.8[AM,DBL]
;;  T329.9[AM,DBL]

;; Searching for RLL:
;;  RECORD[RLL,DBL] seems to have a lot, but not all, of RLL docmented functions
;;  KBCHAN.MAR[RLL,DBL] this is a KB change log file, the only one, but not much in there "RLL KB Changes from 16-Mar-82 18:20:59 by SKLEIN"
;;
;;
;; Discussions:
;;  SKLEIN.2[RDG,DBL]
;;  SKLEIN.3[RDG,DBL]
;;  SKLEIN.3[RLL,DBL]
;;  TIN.TEX[RDG,DBL]
;;  TODO[RDG,DBL] (prior versions, too)
;;  TODO[RLL,DBL]
;;  USERS.RLL[RDG,DBL]4 6 8
;;  BUGS.COR[RDG,DBL]

;; U, UN, -U etc implies "Unit", which is what a symbol/concept/object is in eurisko, Slots are symbol-plist parameters. Given the number of slots, I think we'll leave it as a p-list implementation for now.  I don't think plist vs hashtable performance is going to be an issue, and there's too many to define a class/structure for all of them. If we need to optimize, we can create a structure for the most common ones, and leave the rest on the plist.

;; Replacing TTY with *STANDARD-OUTPUT* and READ as appropriate
;; (append list) => (copy-list list)

;; an O- or Ord- prefix seems to imply ordered (eg a meaningful sequence), vs UnOrd- unordered (eg index is irrelevant, a bag)

;; -NN function suffix means the parameters can be numeric or nil.
;; NNumber seems to be a Natural Number, not related to -NN

;; APPLY* becomes FUNCALL?


;; GETD fetches the function definition. Could be a sexpr, or compilede code, based on other tests. Usually used in code just to check if that symbol has a symbol-function, or to copy to another symbol (which is MOVD's job)
;; PUTD directly stores the function definition, often a sexpr
;; the def can be EXPRP (sexpr), CCODEP (compiled) or SUBRP (native subroutine)

;; TODO - check all instances of EVERY and SOME for proper CL parameter order, as interlisp's is opposite

;; TODO - scan through all the PUTPROPS forms and ensure that all symbols from there exist in the *Units* list, else we have a typo

;; TODO - consider every instance of PACK and EVAL in the source code

;; TODO - cheap hack until breaking this out into separate files and giving it a real .asd
'#. (unless (find-package "ALEXANDRIA")
      (ql:quickload "alexandria"))

(defpackage "EURISCLO"
  (:use :cl :alexandria)
  ;; TODO - rename all these things to make it read more like CL
  (:shadow "NTH"
           "UNION"
           "FLATTEN"
           "MEMBER"
           "COUNT"))

(in-package "EURISCLO")


;; TODO - this stuff is probably RLL config info that gets duplicated here in the DEFVARs, and as well at the end of the file
(defvar *eurcoms* '((vars * eurvars)
                    (fns * eurfns)
                    (prop all * units)
                    (p (advise 'editp 'before '(or (stkpos 'eu)
                                                (print "WARNING: Are you sure you really don't mean 'EU' ??? !!!"))))
                    (p (advise 'makefile 'before '(check-elim)))
                    (p (advise 'printdef 'around '(if (numberp (firstatom expr))
                                                   then
                                                   (resetvars (prettyflg)
                                                    (return *))
                                                   else *)))
                    (globalvars abort-task? added-some agenda are-units crlf c-slot c-slot-sibs c-task conjectures
                     credit-to creditors cur-pri cur-reasons cur-slot cur-sup cur-unit cur-val deleted-units
                     esysprops editp-temp failure-list g-credit g-slot have-genl have-spec heuristic-agenda
                     interp last-edited maybe-failed map-cycle-time min-pri move-defns n-unit-slots need-genl
                     need-spec new-u new-unit new-units new-value new-values not-for-real nf nt old-kb-pu
                     old-kb-pv old-val old-value pos-cred r-arrow rcu space syspros shorter-nam slot-to-change
                     slots-to-change slots-to-elim-initially slots special-non-units synth-u tty task-num
                     temp-caches u-diff undo-kill units unused-slots used-slots user-impatience verbosity
                     warn-slots conjec cprintmp)
                    (p (setq sysprops (union esysprops sysprops)))
                    (p (advise 'logout 'before '(dribble)))
                    (p (advise 'logout 'after '(sos)))
                    (p (and (null (getd 'old-pack*))
                        (putd 'old-pack* (getd 'pack*))
                        (putd 'pack* (getd 'smart-pack*))))
                    (p (initialize-eurisko))
                    (p (cprin1 0 "~%You may call (initial-check-inv) to ferret out references to now-defunct units~%~%Type (eurisko) when you are ready to start.~%~%"))
                    (declare (donteval@load doeval@compile dont-copy compiler-vars (addvars (nlama eue) (nlaml) (lama smart-pack* cprin1))))
                    ))

(defvar *eurvars* '(agenda crlf conjectures deleted-units esysprops failure-list gfns interp min-pri
                    move-defns not-for-real n-unit-slots new-u old-kb-pu old-kb-pv r-arrow space slots
                    slots-to-elim-initially special-non-units synth-u tab temp-caches undo-kill units
                    unused-slots used-slots user-impatience verbosity zz
                    ;; Interlisp vars?
                    (fontchangeflg) (changesarray) (prompt#flg t)))

;; EURVARS in alphabetical order
(defvar *agenda* nil)
(defvar *conjectures* nil)
(defvar *deleted-units* nil)

;; Replicating the IL system provided SYSPROPS just for yuks.  Probably unnecessary, but documenting it
;; These are all the system properties that can be on symbols, which eurisko needs to skip
(defparameter *sysprops* '(prototype vartype newcom whenfiled whenunfiled getdef nulldef deldef putdef whenchanged hasdef editdef canfiledef filegetdef filepkgcontents prettytype delfromprettycom addtoprettycom altomacro macro bytemacro dmacro
                           ;; SBCL stuff that's in operators
                           sb-disassem::instructions))

;; Note that this shares ALTOMACRO and BYTEMACRO with the builtin SYSPROPS
(defvar *esysprops* '(altomacro bytemacro sopval opcode))

(setf *sysprops* (cl:union *esysprops* *sysprops* :test #'eq))

(defvar *failure-list '(nil failed))
(defvar *gfns* '(average-worths check-2-after-editp create-unit define-slot has-high-worth initialize-eurisko
                 interp1 interp2 kill-unit nu rem1prop run-alg start true-if-it-exists union-prop
                 unitp work-on-task work-on-unit xeq-if-it-exists))
;; TODO - get #'interp2 working in load order, rather than 'interp2?
(defvar *interp* 'interp2
  "Default interpreter function to use")
(defvar *min-pri* 150)
;; TODO - added to, but never used otherwise?
(defvar *move-defns* '((movd 'and 'and-2 t)
                       (movd 'and 'and-1 t)
                       (movd 'and 'and-1 t)
                       (movd 'best-subset 'best-subset-3 t)
                       (movd 'best-subset 'best-subset-2 t)
                       (movd 'best-subset 'best-subset-1 t)
                       (movd 'and 'and-2 t)
                       (movd 'and 'and-1 t)))
(defvar *not-for-real* nil)
(defvar *n-unit-slots* nil)
(defvar *new-u* nil)
(defvar *old-kb-pu* '(g h))
(defvar *old-kb-pv* '(eq struc-equal set-equal o-set-equal bag-equal list-equal MEMBER MEMB))
;; TODO - RArrow = '->, SPACE = #\Space, TAB = string of 8 spaces
;; TODO - Like AM, -record suffix is for history lists, -failed-record is for caching failures?
(defvar *slots* '(abbrev alg applic-generator applics arity compiled-defn conjecture-about conjectures
                  creditors data-type defn direct-applics domain dont-copy double-check each-element-is-a
                  elim-slots english examples extensions failed-record failed-record-for fast-alg
                  fast-defn format generalizations generator higher-arity if-about-to-work-on-task
                  if-finished-working-on-task if-parts if-potentially-relevant if-task-parts
                  if-truly-relevant if-working-on-task in-domain-of indirect-applics int-applics
                  int-examples interestingness inverse isa is-a-int is-range-of iterative-alg
                  iterative-defn less-interesting lower-arity more-interesting nec-defn non-examples
                  overall-record range rarity record record-for recursive-alg recursive-defn
                  restrictions sib-slots specializations sub-slots subsumed-by subsumes suf-defn
                  super-slots then-add-to-agenda then-add-to-agenda-failed-record then-add-to-agenda-record
                  then-compute then-compute-failed-record then-compute-record then-conjecture
                  then-conjecture-failed-record then-conjecture-record then-define-new-concepts
                  then-define-new-concepts-failed-record then-define-new-concepts-record
                  then-delete-old-concepts then-delete-old-concepts-failed-record
                  then-delete-old-concepts-record then-modify-slots then-modify-slots-failed-record
                  then-modify-slots-record then-parts then-print-to-user then-print-to-user-failed-record
                  then-print-to-user-record to-delete to-delete-1 transpose unitized-alg unitized-defn
                  why-int worth))
(defvar *slots-to-elim-initially* nil)
(defvar *special-non-units* '(t nil))
(defvar *synth-u* '(h19-criterial h5-criterial h5-good h-avoid-2-and h-avoid-3-first h-avoid-if-working))
(defvar *temp-caches* '((REMPROP 'anything 'examples)))
(defvar *undo-kill* nil)
(defvar *units* '(int-applics mult-ele-struc-insert h29 h28 h27 h26 h25 rarity why-int h24 h23 is-a-int
                  int-examples less-interesting more-interesting h22 interestingness restrictions
                  extensions op-cat-by-nargs pred-cat-by-nargs tertiary-pred unary-pred binary-pred
                  higher-arity lower-arity non-empty-struc empty-struc set-of-sets
                  structure-of-structures truth-value atom implies not logic-op relation
                  set-of-o-pairs invert-op inverted-op  restrict identity-1 proj-3-of-3 proj-2-of-3
                  proj-1-of-3 proj2 proj1 MEMB MEMBER all-but-last last-ele all-but-third all-but-second
                  all-but-first third-ele second-ele first-ele reverse-o-pair pair o-pair
                  parallel-join-2 parallel-join repeat2 tertiary-op repeat binary-op
                  parallel-replace-2 each-element-is-a unary-op type-of-structure parallel-replace
                  coalesce bag-difference o-set-difference list-difference set-difference
                  struc-difference bag-union list-union o-set-union struc-union bag-intersect
                  o-set-intersect list-intersect struc-intersect set-union set-intersect ord-struc-op
                  ord-struc-equal bag-equal list-equal o-set-equal suf-defn nec-defn un-ord-struc
                  ord-struc no-mult-ele-struc o-set-delete o-set-op o-set-insert o-set
                  mult-ele-struc-delete-1 mult-ele-struc-op mult-ele-struc bag-delete-1 bag-delete bag-op
                  bag-insert bag list-delete-1 list-delete list list-insert list-op set-delete
                  set-insert struc-delete struc-op struc-insert and abbrev add alg always-nil
                  always-nil-2 always-t always-t-2 anything applic-generator applics arity
                  best-choose best-subset bit category compiled-defn compose conjecture
                  conjecture-about conjectures constant-binary-pred constant-pred
                  constant-unary-pred creditors criterial-slot data-type defn direct-applics
                  divisors-of domain dont-copy double-check eq equal elim-slots english even-num
                  examples failed-record failed-record-for fast-alg fast-defn format
                  generalizations generator good-choose good-subset h1 h10 h11 h12 h13 h14 h15
                  h16 h17 h18 h19 h19-criterial h2 h20 h21 h3 h4 h5 h5-criterial h5-good h6 h7 h8
                  hind-sight-rule IEQP IGEQ IGREATERP ILEQ ILESSP if-about-to-work-on-task
                  if-finished-working-on-task if-parts if-potentially-relevant if-task-parts
                  if-truly-relevant if-working-on-task in-domain-of indirect-applics inverse isa
                  is-range-of iterative-alg iterative-defn math-concept math-obj math-op math-pred
                  multiply nnumber non-criterial-slot non-examples num-op OR odd-num op
                  overall-record perf-num perf-square pred prime-num proto-conjec random-choose
                  random-subset range record record-for record-slot recursive-alg recursive-defn
                  repr-concept set set-equal set-of-numbers set-op sib-slots slot specializations
                  square struc-equal structure sub-slots subsetp subsumed-by subsumes successor
                  super-slots task the-first-of the-second-of then-add-to-agenda
                  then-add-to-agenda-failed-record then-add-to-agenda-record then-compute
                  then-compute-failed-record then-compute-record then-conjecture
                  then-conjecture-failed-record then-conjecture-record then-define-new-concepts
                  then-define-new-concepts-failed-record then-define-new-concepts-record
                  then-delete-old-concepts then-delete-old-concepts-failed-record
                  then-delete-old-concepts-record then-modify-slots then-modify-slots-failed-record
                  then-modify-slots-record then-parts then-print-to-user then-print-to-user-failed-record
                  then-print-to-user-record to-delete to-delete-1 transpose unary-unit-op undefined
                  undefined-pred unit unit-op unitized-alg unitized-defn worth los1 los2 los3 los4
                  los5 los6 los7 win1))

(defvar *unused-slots* '(alg applic-generator compiled-defn defn direct-applics if-parts if-task-parts
                         indirect-applics int-applics sib-slots then-conjecture-failed-record
                         then-define-new-concepts-failed-record then-delete-old-concepts-failed-record
                         then-modify-slots then-modify-slots-failed-record then-modify-slots-record then-parts
                         then-print-to-user-failed-record to-delete why-int))

(defvar *used-slots* '(abbrev arity conjecture-about conjectures creditors data-type domain dont-copy
                       double-check each-element-is-a elim-slots english examples extensions
                       failed-record failed-record-for fast-alg fast-defn format generalizations
                       generator higher-arity if-about-to-work-on-task if-finished-working-on-task
                       if-potentially-relevant if-truly-relevant if-working-on-task in-domain-of int-examples
                       interestingness inverse isa is-a-int is-range-of iterative-alg iterative-defn
                       less-interesting lower-arity more-interesting nec-defn non-examples overall-record
                       range rarity record record-for recursive-alg recursive-defn restrictions
                       specializations sub-slots subsumed-by subsumes suf-defn super-slots
                       then-add-to-agenda then-add-to-agenda-failed-record then-add-to-agenda-record
                       then-compute then-compute-failed-record then-compute-record then-conjecture
                       then-conjecture-record then-define-new-concepts then-define-new-concepts-record
                       then-delete-old-concepts then-delete-old-concepts-record then-print-to-user
                       then-print-to-user-record to-delete-1 transpose unitized-alg unitized-defn worth))
(defvar *user-impatience* 1)
(defvar *verbosity* 67
  "Must be higher than the CPRIN1 parameter in order to print.")
(defvar *zz* nil)
(defvar *u-diff* nil
  "TODO - unknown, used in both utilities and heuristics")

#|
(setf fontchangeflg nil)
(setf changesarray nil)
(setf prompt#flg t)
|#

(defvar *eurfns* '(apply-eval add-inv add-nn add-prop-l alg all-pairs applic-args applic-gen-args applic-gen-build
                   applic-gen-init apply-to-u apply-alg apply-defn apply-rule average average-worths
                   best-choose best-subset CPRIN1 cache-examples certainty check-2-after-editp
                   check-after-editp check-elim check-the-values comp cons-nn create-unit cur-sup
                   cycle-through-agenda date2 decrement-credit-assignment define-if-slot define-slot defn
                   direct-applics divides does-intersect dreplace-get dwim-union-prop EU #|EVERY2|#
                   equal-to-within-subst eurisko examples extract-input extract-output
                   extract-priority extract-reasons extract-slot-name extract-unit-name favor-first
                   first-two flatten fraction-of gather-examples gen-args gen-build gen-init
                   generalizations generalize-1-lisp-expr generalize-1-lisp-fn generalize-1-lisp-pred
                   generalize-bit generalize-compiled-lisp-code generalize-data-type
                   generalize-dotted-pair generalize-io-pair generalize-lisp-fn generalize-lisp-pred
                   generalize-list generalize-nil generalize-number generalize-slot generalize-text
                   generalize-unit get-a-bag get-a-list get-a-o-pair get-a-o-set get-a-set get-a-struct
                   good-choose good-subset half has-high-worth ISQRT indirect-applics
                   initial-check-inv initial-elim-slots initialize-credit-assignment
                   initialize-eurisko inside-of instances interestingness interp1 interp2 interp2 ;; TODO - duplicated interp2?
                   interp3 interrupts is-a-kind-of is-alto is-subset-of kill-slot kill-unit known-applic
                   leq-nn less-worth listify-if-nec lists-starting lists-starting-aux MAP2EVERY
                   MAPAPPEND MAXIMUM MAXIMUM2 map-and-print map-applics map-examples map-union
                   merge-props merge-tasks more-specific most-specific my-time NU n-unitp nearness-to
                   new-nam no-repeats-in ok-bin-preds order-tasks PRINBOL PRINTASK pu pu2 percentify
                   punish-severely quoted REM1PROP random-choose randomp random-pair random-subset
                   random-subst random-subst* repeats-in report-on reset-pri rule-taking-too-long
                   run-alg run-defn SOS SQUARE STAART self-intersect set-diff set-difference
                   set-intersect set-union shorten sib-slots sibs slot-names slot-subst slotp
                   smart-pack* snazzy snazzy-agenda snazzy-concept snazzy-heuristic snazzy-task
                   some-o-pair some-pair some-uneliminated sort-by-worths specializations
                   specialize-1-lisp-expr specialize-1-lisp-fn specialize-1-lisp-pred specialize-bit
                   specialize-compiled-lisp-code specialize-data-type specialize-dotted-pair
                   specialize-io-pair specialize-lisp-fn specialize-lisp-pred specialize-list
                   specialize-nil specialize-number specialize-slot specialize-text specialize-unit
                   strong-unsave-def taking-too-long taking-too-much-space the-first-of the-number-of
                   the-second-of tiny-reward true-if-it-exists un-get union-prop union-prop-l unitp wax-on
                   whole-task work-on-task work-on-task work-on-unit work-on-unit #|Duplicate?|# worth-working-on
                   xeq-if-it-exists yes-no zero-records))



;; TODO - these sections should be broken out into their own files, but for now search/replace is much easier in 1


;;;;------------------------------------
;;;; Interlisp compatibility functions

;; TODO - remove the ones with CL analogs, port the usage sites to idiomatic CL

(declaim (inline fixp))
(defun fixp (x)
  "Fixnum/integer test."
  ;; TODO - Interlisp has "small" immediate 17-bit and "big" boxed 32-bit fixed width signed ints, no actual variable-sized bigints. Overflow has a runtime option to either wrap (default) or error.  For now, we'll assume fixnum?
  (typep x 'fixnum))

(declaim (inline square))
(defun square (x)
  "Mathematical square."
  (* x x))

(defun attach (val list)
  "Appends VAL to the beginning of LIST, mutating the first cell such that the result is still EQ to LIST."
  ;; TODO - this is horrible, and the usage site (only one) should be rewritten to return a new value instead.
  (assert (listp list))
  (if list
      (let ((new-cell (cons (car list) (cdr list))))
        (setf (car list) val)
        (setf (cdr list) new-cell)
        list)
      ;; No input list, make a new one
      (list val)))

(defun nconc1 (list item)
  "NCONCs a single item instead of a list."
  (nconc list (list item)))

(defun memb (item list)
  "MEMBER with EQ test"
  (cl:member item list :test #'eq))

(defun member (item list)
  "MEMBER with EQUAL test"
  (cl:member item list :test #'equal))

(defmacro subset (list pred)
  "Returns the items of the list that met the predicate."
  `(remove-if-not ,pred ,list))

(declaim (inline rand))
(defun rand (min max)
  "Random number inclusive on both ends."
  (+ min (random (1+ (- max min)))))

(defun nth (list n)
  "Return the nth cell in the list, the first being 1 which would return the original list. n=0 prepends a (NIL . <list>) for consistency."
  (if (zerop n)
      (cons nil list)
      (nthcdr (1- n) list)))

(defun copy (list)
  "Deep copy of the cons structure, all non-cons values are reused."
  ;; TODO - the spec says this only recurses on the CARs, to support very long lists. Make a separate internal tail-recursive operator if we blow the stack on naive recursion
  (if (consp list)
      (cons (copy (car list))
            (copy (cdr list)))
      list))

(defun union (x y)
  "This is more naive than CL's UNION. This prepends elements in X that aren't in Y to it, so duplicates in Y remain, but duplicates from X get rooted out as they're added to Y and checked."
  (dolist (item x)
    (unless (memb item y)
      (push item y)))
  y)

(defmacro mapconc (list func &optional (stepping-fn '#'cdr))
  ;; TODO - is this exactly equivalent to CL:MAPCON?
  (with-gensyms (val)
    `(loop for ,val in ,list by ,stepping-fn
           nconc (funcall ,func ,val))))

(defun default-sort (a b)
  ;; IL's alphanumeric sort operator sorts numbers before strings, and strings in alpha order
  (cond
    ((and (symbolp a)
          (symbolp b))
     (string< (symbol-name a) (symbol-name b)))
    (t (error "DEFAULT-SORT can't handle types of ~s ~s yet" a b))))

(defun count (tree)
  "Counts the number of cons cells that compose the structure of the tree."
  (cond
    ((consp tree) (+ 1 (count (car tree))
                     (count (cdr tree))))
    (t 0)))

(defun getprop (symbol key)
  "Return a single property value"
  (get symbol key))

(defun getproplist (symbol)
  "Return the entire proplist"
  (symbol-plist symbol))

(defun propnames (symbol)
  "Returns just the symbol's plist's keys"
  (loop for prop in (symbol-plist symbol) by #'cddr
        collect prop))

(defun addprop (atom prop new &optional to-head)
  "Adds the NEW value to the end of the proplist for property PROP on ATOM."
  (if to-head
      (push new (get atom prop))
      (setf (get atom prop) (nconc1 (get atom prop) new))))

;; TODO - no idea why PUTPROP vs PUT is used in the code. PUT is not standard IL.
(declaim (inline putprop put))
(defun putprop (symbol key value)
  "Set a single property value"
  (setf (get symbol key) value))

(defun put (symbol key value)
  "Set a single property value"
  (putprop symbol key value))

(defmacro putprops (symbol &body plist)
  "Add the given plist to the symbol's plist. All are unevaluated."
 ;; Experimenting with allowing lambda values to be compiled. Value must be a lambda, not a lambda inside a containing list, for now.
  `(progn
     ,@ (loop for (k v) on plist by #'cddr
              collect `(setf (get ',symbol ',k) ,(if (and (consp v)
                                                          (eq (car v) 'lambda))
                                                     v
                                                     (list 'quote v))))))

(defun setproplist (symbol plist)
  "Replace the plist of a symbol."
  (setf (symbol-plist symbol) plist))

;; REMPROP is the only symbol-plist function used in here that is compatible with CL.

(defun movd (from to &optional clone?)
  "Copies the function defintion of a symbol. If the COPY? flag is set, conses a new version of it (source code only). Returns the TO symbol."
  (declare (ignore clone?))
  (setf (fdefinition to) (fdefinition from))
  to)

(defun listget (plist key)
  "Returns the associated value from the plist"
  (when (consp plist)
    (getf plist key)))

(defun listput (plist key val)
  "Sets the key's value in the plist to val, either by overwriting the old value, or appending a new field at the end of the list. Returns val."
  ;; TODO - if it's odd length or improper ended, it adds to the beginning. Does it use attach for that? Does it return the new list instead of val?
  (assert (listp plist))
  (loop for cell on plist by #'cddr
        do (when (eq key (car cell))
               ;; TODO - error check list has another cell
             (setf (cadr cell) val)
             (return))
           ;; TODO - broken if it's odd length
        finally (setf (cdr (last plist))
                      (list key val)))
  val)

(defun printdef (expr)
  "Pretty print an expression. There are lots more flags in the IL standard, but eurisko doesn't use them."
  (let ((*print-pretty* t))
    (format t "~s~%" expr)))

(defun subpair (old new expr &optional flag)
  "Similar to SUBLIS, except that elements of NEW are substituted for corresponding atoms of OLD in EXPR. New structure is created only if needed, or if FLAG=T"
  ;; TODO - the interlisp does tail-matching on (a b . c) with the tail of the NEW list, and not sure what the exact copy rules are yet.  Just punting to CL's subslis for now
  (assert (null flag))
  ;; Convert to a-list format
  (sublis (mapcar #'cons old new) expr))


;; Already done:
;;  LISTP -> CONSP (but IL:LISTP returns the value if it passes, not T)
;;  SOME1 -> FIND-IF, returns the first in the list that passes the predicate, else NIL
;;  MAP2C -> MAP-PLIST if 2nd is the CDR of the first and by #'CDDR
;;     or -> MAPC with 2 different lists
;;  (EVERY2 list1 list2 fn) -> (CL:EVERY fn list1 list2)
'(defmacro map2c (list1 list2 mapfn &optional (stepping-fn '#'cdr))
  "Map across 2 lists, iterating by the stepping function"
  (alexandria:with-gensyms (item1 item2)
    (alexandria:once-only (stepping-fn)
      `(loop for ,item1 in ,list1 by ,stepping-fn
             for ,item2 in ,list2 by ,stepping-fn
             do (funcall ,mapfn ,item1 ,item2)))))



;;;;----------------------
;;;; CL port utility functions
;;;;
;;;; Finding repeated patterns in the code to shrink it

(defun resolve-examples (obj)
  "For things expecting a list of units, if a unit which isa Set is given, then grab the list of examples."
  (if (and (symbolp obj)
           (memb 'set (isa obj)))
      (or (examples obj)
          (gather-examples obj))
      obj))


;;;;-----------------
;;;; Numeric utilities

(defun add-nn (x y)
  "Adds together potentially NIL values, treating NIL as zero."
  (+ (or x 0)
     (or y 0)))

(defun leq-nn (x y)
  "NIL-safe less-than-or-equal. Any NIL makes this return NIL."
  (and (numberp x)
       (numberp y)
       (< x y)))

(defun average (n m)
  ;; TODO - why is the +1 in the numerator? probably rounding
  ;; Original used QUOTIENT, which uses integer (rounded) or floating point depending on inputs
  ;; So if we have integers, let's keep them as such in order to avoid rationals manifesting
  (if (and (fixp n)
           (fixp m))
      (ash (+ n m 1) -1)
      (/ (+ n m 1) 2)))

(defun divides (a b)
  "Tests if B is evenly divisible by A."
  (zerop (rem b a)))

(defun certainty (n)
  "Returns a label for the given numeric certainty value."
  (cond
    ((< n 100) 'inconceivable)
    ((< n 400) 'unlikely)
    ((< n 600) 'possible)
    ((< n 800) 'probable)
    (t 'almost-certain)))

(defmacro favor-first (a b)
  "Evaluates A randomly 45 out of 46 times, evaluates B otherwise"
  `(if (zerop (rand 0 45))
       ,b
       ,a))

(defun half (n)
  (floor n 2))

(defun nearness-to (n x)
  ;; ORIG: This certainly works for nearness of N to .1
  (- 1000 (* 1000 (square (- n x)))))

(defun randomp (&optional a b)
  "50/50 chance of being true"
  ;; These params are here for supporting use in SORT
  (declare (ignore a b))
  (eq 0 (rand 0 1)))



;;;;----------------
;;;; List utilities

(defun add-prop-l (list propname val)
  "Like ADDPROP, but works on standalone p-list values instead of symbol p-lists"
  ;; TODO - change to object slots
  (cond
    ;; Prop already exists
    ((assoc propname list)
     (nconc1 (assoc propname list) val)
     list)
    ;; Add to the end of the existing list, to keep head pointer intact
    (list (nconc1 list (list propname val)))
    ;; Make a new list
    (t (list (list propname val)))))

;; TODO - only used once
(defun all-pairs (l rel)
  "Returns a list of (index1 index2 val1 val2 retval) for all pairs in the list where the (rel index1 index2) call returns non-NIL."
  (loop for ip from 1 to (length l)
        for ii in l
        nconc (loop for jp from 1 to (length l)
                    for jj in l
                    nconc (let ((v nil))
                            (cond
                              ((eq ip jp) nil)
                              ;; Capture the return value in V
                              ((setf v (funcall rel ii jj))
                               (list (list ip jp ii jj v))))))))

(defun cons-nn (head rest)
  "Cons the head onto the rest of list, only if the head is non-nil."
  (if head
      (cons head rest)
      rest))

(defun does-intersect (l m)
  "Tests if the two lists share at least 1 member, by EQ"
  (some (lambda (z) (memb z m)) l))

(defun equal-to-within-subst (c1 c2 v1 v2)
  "Is the value of V1 and V2 equal, including if C2 were subst'd for C1?"
  (cond
    ((eq v1 v2))
    ;; OPTIMIZE - faster implementation of same-length with early exit
    ((not (eq (length v1) (length v2)))
     nil)
    ((equal v1 v2))
    ((equal v2 (subst c2 c1 v1 :test #'eq)))))

(defun first-two (list)
  "Returns a list of the first two elements of the given list, filling NILs if not present."
  (list (car list) (cadr list)))

(defun flatten (list)
  (cond
    ((null list) nil)
    ((consp list) (mapconc list #'flatten))
    ;; Wrap everything else in a list for NCONC to join into the parent list
    (t (list list))))

(defun fraction-of (l p)
  "Compute the fraction of entries on L which satisfy predicate P."
  (if (atom l)
      0
      (/ (float (length (subset l p)))
         (float (length l)))))

;; TODO - what is OV supposed to be anyway?
(defun get-a-bag (ov)
  (get-a-list ov))

(defun get-a-list (ov)
  "Return a list of 0-100 arbitrary Units."
  (declare (ignore ov)) ;; unused in original anyway?
  (loop for i from 0 to (rand 0 (square (rand 1 10)))
        collect (favor-first (random-choose (cache-examples 'anything))
                             (get-a-struc))))

;; TODO - no guarantee of non-duplicate?
(defun get-a-o-pair (ov)
  (first-two (get-a-list ov)))

(defun get-a-o-set (ov)
  (self-intersect (get-a-list ov)))

(defun get-a-set (ov)
  (self-intersect (get-a-list ov)))

(defun get-a-struc (&optional ov)
  ;; TODO - dynamic construction of GET-A-* function names, need rearchitecting
  (let ((f (pack* 'get-a-
                  (random-choose (getprop 'structure 'specializations)))))
    (cond
      ((fboundp f) (apply f ov))
      ;; Loop until we found a specialization with an implementation
      (t (get-a-struc ov)))))

(defun inside-of (x l)
  "Deep tree search for EQ X inside L, matches both CARs and CDRs."
  (cond
    ((null l) nil)
    ((eq x l) t)
    ((consp l) (or (inside-of x (car l))
                   (inside-of x (cdr l))))
    (t nil)))

(defun is-subset-of (l m)
  (subsetp l m :test #'equal))

;; TODO - this will turn NIL into (NIL), is that the intent?
(defun listify-if-nec (x)
  (if (consp x)
      x
      (list x)))

(defun lists-starting (x l)
  "Searches the tree, returning all contained lists starting with EQ X."
  (labels ((aux (l)
             (cond
               ((not (consp l)) nil)
               ((eq x (car l))
                (cons l (mapconc (cdr l) #'aux)))
               (t (mapconc l #'aux)))))
    (aux l)))

(defun merge-props (l m)
  "Copy all SLOTP properties of M onto L, returning L."
  ;; ORIG: L and M are each property lists
  (map-plist m
             (lambda (p v)
               (when (slotp p)
                 (if (listget l p)
                     ;; BUGFIX - orig had (LISTPUT L (UNION ...)), forgetting the key P
                     (listput l p (union (listify-if-nec (listget l p))
                                         (listify-if-nec v)))
                     ;; adding props on the tail, instead of a head push, to mutate the list without changing the head
                     (setf l (nconc l (list p v)))))))
  ;; Original had another commented out version that added to the head, so this is mutating L in place
  l)

(defun no-repeats-in (l)
  "No EQUAL duplicates on the list"
  (loop for sublist on l
        when (member (car sublist) (cdr sublist))
          return nil
        finally (return t)))

(defun random-pair (l rel)
  (random-choose (all-pairs l rel)))

(defun random-subst (x y z &optional (num-tries 4))
  (let (tes)
    (cond
      ((zerop num-tries) z)
      ((equal z (setf tes (random-subst* x y z)))
       (random-subst x y z (1- num-tries)))
      (t tes))))

(defun random-subst* (x y z)
  (cond
    ((equal x y) z)
    ((equal y z) (if (randomp) y x))
    ((not (consp z)) z)
    (t (cons (random-subst* x y (car z))
             (random-subst* x y (cdr z))))))

(defun rem1prop (a p v)
  (or (not (symbolp a))
      (not (symbolp p))
      (and (memb v (getprop a p))
           (delete v (getprop a p)))
      (delete v (funcall p a))
      (remprop a p)))

(defun repeats-in (l)
  "Boolean test if any repeated EQUAL elements exist."
  (loop for sublist on l
        when (member (car sublist) (cdr sublist))
          do (return t))
  nil)

(defun self-intersect (x)
  ;; TODO - this is actually deduplication because IL is weak. CL won't dedup this way. Rename the function.
  (loop for sublist on x
        when (not (member (car sublist) (cdr sublist)))
          collect (car sublist)))

(defun set-diff (l m)
  ;; ORIG: presumes that L and M are lists of atoms. Nondestructive
  (subset l (lambda (v) (not (member v m)))))

(defun set-intersect (l m)
  (subset l (lambda (z) (memb z m))))

(defun set-union (s1 s2)
  (append (set-difference s1 s2) s2))

(defun the-first-of (x y)
  (declare (ignore y))
  x)

(defun the-number-of (list pred)
  "Counts the items which pass the predicate."
  (loop for item in list
        count (funcall pred item)))

(defun the-second-of (x y)
  (declare (ignore x))
  y)

(defun union-prop (a p v &optional flag kidding)
  (or kidding
      (member v (funcall p a))
      (eq 'failed (car (last v)))
      (addprop a p v flag)))

;; TODO - only called once, from h24
(defun union-prop-l (a p v &optional flag kidding)
  (or kidding (dolist (x v)
                (union-prop a p x flag))))





;;;;-----------------------
;;;; Iteration utilities

(defun map-plist (list func)
  "Iterates calling (func k v) for every 2 items in the list"
  (loop for (k v) in list by #'cddr
        do (funcall func k v)))

(defun map-union (l f)
  "Like MAPCONC, but instead of NCONCing the results we simply, nondestructively, union them."
  (let ((so-far nil))
    (dolist (q l)
      ;; OPTIMIZATION - :test #'eq? the interlisp spec doesn't say anything about 
      (setf so-far (union (funcall f q) so-far)))))

(defun map2every (list funclist)
  "Traversing both lists, apply the respective function to the respective list entry. If any function returns NIL, the entire function fails. Every application must return non-NIL to succeed."
  (mapc (lambda (item func)
          (unless (funcall func item)
            (return-from map2every nil)))
        list funclist)
  t)

;; TODO - is this exactly equivalent to CL:MAPPEND?
(defun mapappend (l f)
  (cond ((null l) nil)
        (t (nconc (copy-list (funcall f (car l)))
                  (mapappend (cdr l) f)))))

(defun maximum (list test)
  "Returns the element of the list with the highest test value."
  (cond
    ;; Empty list or not a list is NIL
    ((not (consp list)) nil)
    ;; List of 1 element just returns that element
    ((not (consp (cdr list))) (car list))
    ;; Iterate assuming the first number is best...
    (t (let* ((best-item (car list))
              (best-score (funcall test best-item)))
         ;; ...and test each subsequent value
         (dolist (item (cdr list))
           (let ((score (funcall test item)))
             (when (> score best-score)
               (setf best-item item)
               (setf best-score score))))
         best-item))))

(defun maximum2 (list comparator)
  "Returns the element of the list which compares best against the others, via (comparator worse better)."
  ;; Note that this is a single scan, and if the comparator isn't transitive, results might be goofy.
  (cond
    ((not (consp list)) nil)
    ((not (consp (cdr list))) (car list))
    (t (let ((best (car list)))
         (dolist (item (cdr list))
           (when (funcall comparator item best)
             (setf best item)))
         best))))

(defun map-and-print (l f)
  "Print the result of every application of F to the elements of L."
  (dolist (z l)
    (prin1 (funcall f z))))



;;;;-------------------------------------
;;;; Unit and list-of-unit utilities


;; Predicates

(declaim (inline unitp n-unitp))
(defun unitp (u)
  ;; ORIG: u is a unit iff it has a Worth property on its plist
  (worth u))

(defun n-unitp (u)
  (not (unitp u)))

(defun is-a-kind-of (unit kind)
  (or (eq unit kind)
      (memb kind (generalizations unit))))



;; Worth functions

(defun average-worths (u1 u2)
  "Average the worths of the two units."
  (/ (add-nn (worth u1) (worth u2)) 2))

(defun has-high-worth (u)
  (and (unitp u)
       (> (worth u) 800)))

(defun less-worth (u1 u2)
  (cond
    ((not (unitp u2)) nil)
    ((not (unitp u1)) t)
    (t (< (worth u1)
          (worth u2)))))

(defun sort-by-worths (l)
  (sort l #'less-worth))

(defun punish-severely (u)
  (when (unitp u)
    (put u 'worth (half (worth u)))))

(defun tiny-reward (u)
  (put u 'worth (1+ (worth u))))


;; List-of-unit functions

(defun best-choose (l)
  "Return the highest worth unit in the list. Can accept a unit, and it will return the highest worth example of it."
  (setf l (resolve-examples l))
  ;; Only deal with units, ignore any other element
  (maximum (subset l #'unitp) #'worth))

(defun best-subset (l)
  "Get some number of the highest worth units, sorted highest first."
  (setf l (resolve-examples l))
  ;; Get a random number of the highest worth units?
  (nreverse (nth (sort-by-worths (copy-list l))
                 (rand 1 (length l)))))

(defun good-choose (l)
  "Get one of the best units from the list. Best has 50% chance, 2nd best as 25% chance, etc."
  (setf l (resolve-examples l))
  (car (some #'randomp (sort-by-worths (copy-list l)))))

(defun good-subset (l)
  "Get some number of the highest worth units from the list."
  (random-subset (best-subset l)))

(defun random-choose (l)
  (setf l (resolve-examples l))
  (car (nth l (rand 1 (length l)))))

(defun random-subset (l)
  (setf l (resolve-examples l))
  (subset l #'randomp))

(defun most-specific (l)
  (maximum2 l #'more-specific))



;; Specific to heuristics, hence H instead of U?
(defun zero-records (h)
  ;; ORIG: remove all properties of the form ---Record
  (dolist (s (examples 'record-slots))
    (remprop h s))
  '|.|)



;; TODO - rename to NEW-NAME
(defun new-nam (a)
  ;; TODO - I _think_ this is equivalent. Original increments a counter until the name it packs isn't UNITP.
  (gensym a))

(defun create-unit (name &optional nold)
  ;; TODO - comment
  (prog1 (cond
           ((not (symbolp name))
            (warn "Must be atomic unit name! You typed: ~s" name))
           ;; If this name already exists, gensym up a fresh name and try again
           ((memb name *units*)
            (create-unit (new-nam name) nold))
           ((memb nold *units*)
            (push name *units*)
            (push name *new-u*)
            (setproplist name (merge-props (copy-list (getproplist name))
                                           (slot-subst name nold (getproplist nold))))
            (dolist (p (propnames name))
              (cond
                ((dont-copy p) (remprop name p))
                ((double-check p) (check-the-values name p (funcall p name)))))
            (add-inv name))
           (t
            (push name *units*)
            (push name *new-u*)
            (put name 'worth 500)
            name))
    (define-if-slot name)
    (and (symbol-function nold)
         (not (symbol-function name))
         ;;(movd nold name t) ;; T = if the src of the copy is a sexpr, cons up a new copy with the move
         (setf (symbol-function name) (symbol-function nold))
         ;; Note that these MOVD forms are never executed; I wonder if RLL does use them, though
         (push `(movd ',nold ',name) *move-defns*))))


(defun kill-unit (u)
  (and (unitp u)
       (not (memb u *new-u*))
       (push (list u (copy (getproplist u))) *undo-kill*))
  (setf *units* (delete u *units*))
  (setf *new-u* (delete u *new-u*))
  (setf *synth-u* (delete u *synth-u*))
  (setf *slots* (delete u *slots*))
  (loop for s in (copy-list (getproplist u)) by #'cddr
        do (kill-slot s))
  (setf *agenda* (subset *agenda* (lambda (ta)
                                    (not (eq u (extract-unit-name ta))))))
  '|.|)



(defun interestingness (u &optional looked-thru)
  (cond
    ((memb u looked-thru) nil)
    ((cdr (push u looked-thru))
     (cons-nn (getprop u 'interestingness)
              (map-union (generalizations u)
                         (lambda (su)
                           (interestingness su looked-thru)))))
    ((setf looked-thru (cons-nn (getprop u 'interestingness)
                                (map-union (generalizations u)
                                           (lambda (su)
                                             (interestingness su looked-thru)))))
     ;; ORIG: this must be the initial call
     `(lambda (u) (or ,@looked-thru)))
    (t
     ;; ORIG: There were no Interestingness predicates anywhere along my ancestry
     nil)))

(defun more-specific (u v)
  (cond
    ((memb u (getprop v 'generalizations)) nil)
    ((memb v (getprop u 'generalizations)) t)
    ((some (lambda (s)
             (memb u (getprop v s)))
           (sub-slots 'generalizations))
     nil)
    ((some (lambda (s)
             (memb v (getprop u s)))
           (sub-slots 'generalizations))
     t)
    ((memb u (isa v)) nil)
    ((memb u (isa u)) t)
    (t ;; ORIG: I give up. Pretend that the bigger one is more specific
     (> (length (getproplist u))
        (length (getproplist v))))))



;; TODO - not sure what "siblings" this is fetching, it seems to get non-system properties of the unit/symbol
(defun sibs (u)
  (subset (propnames u)
          (lambda (s)
            (not (memb s *sysprops*)))))

(defun some-uneliminated ()
  (some (lambda (u)
          (or (some (lambda (s) (getprop u s)) *slots-to-elim-initially*)
              (some (lambda (s) (getprop u s)) (elim-slots u))))
        *units*))


(defun dwim-union-prop (a p v &optional flag)
  ;; TODO - comment
  (cond
    ((unitp a) (union-prop a p v flag))
    ((memb a *special-non-units*)
     (cprin1 50 "~%" a " isn't a unit, but it has an excuse, so we'll let it slide.~%"))
    ((symbolp a)
     ;; TODO - this was a raw PRIN1 in the original? everything from here down was prin1
     (cprin1 0 a " is not yet a unit; make it one?")
     (and (yes-no)
          (union-prop a p v flag)
          (putprop a 'isa '(slot))
          (new-unit a (and (inverse p)
                     (unitp v)
                     (let ((tmp8 (car (some #'unitp (funcall (car (inverse p)) v)))))
                       (cprin1 0 " ... Copying from " tmp8 "~%")
                       tmp8)))))))

(defun new-unit (n nold &optional fullflg)
  (prog1 (cond
           ((not (symbolp n))
            (cprin1 -1 "Must be atomic unit name! You typed: " n)
            n)
           ((memb n *units*)
            (cprin1 -1 "Sorry, " n " is already a unit!")
            n)
           ((memb nold *units*)
            (push n *units*)
            (setproplist n (merge-props (getproplist n)
                                        (subst n nold (getproplist nold))))
            (setf *warn-slots* nil)
            (dolist (p (propnames n))
              (cond
                ((dont-copy p) (if fullflg
                                   (push p *warn-slots*)
                                   (remprop n p)))
                ((double-check p) (push p *warn-slots*))))
            (when *warn-slots*
              (warn "Doublecheck the values stored in: ~s" *warn-slots*))
            ;; TODO - evil eval, what does EU do?
            (eval `(eu ,n))
            (add-inv n)
            `(,n has-been-initialized))
           (t (push n *units*)
              (put n 'worth 500)
              ;; TODO - eval again, probably should be (funcall #'eu (symbol-value n)) ?
              (eval `(eu ,n))
              (add-inv n)
              `(,n has-been-initialized)))
    (define-if-slot n)))




;;;;-----------------------------
;;;; Individual slot utilities

(defun add-inv (un)
  "Add any known inverse slots onto the given symbol, from the slots it already has."
  ;; Parallel iteration over plist keys & values
  (map-plist (symbol-plist un)
             (lambda (propname vals)
               (alexandria:when-let (inv (car (inverse propname)))
                 ;; OPTIMIZE - have the dwim-union-prop iterate the list instead
                 (mapc (lambda (val)
                         (dwim-union-prop val inv un))
                       vals)))))


(defun apply-alg (f args)
  ;; TODO - does the constructed expression need to be EVAL'd?
  (apply #'run-alg (cons f args)))

(defun apply-defn (u args)
  ;; TODO - does the constructed expression need to be EVAL'd?
  (apply #'run-defn (cons u args)))

(defun apply-rule (r u msg)
  ;; TODO - comment
  ;; ORIG: Unfortunately, this doesn't check the value of AbortTask...
  (let* ((*arg-unit* u))
    ;; FIX: U was C in here, probably read the caller's C var which was passed in the 2nd param
    (and (cprin1 75 "~%   Rule " r (abbrev r)
                 " is being applied to " U (or msg " ") "~%")
         (every #'xeq-if-it-exists (sub-slots 'then-parts))
         (cprin1 75 "    The Then Parts of the rule have been executed.~%~%"))))

(defun cache-examples (u)
  "Fill in the example cache of the unit."
  (unless (getprop u 'examples)
    (put u 'examples (gather-examples u))))

(defun gather-examples (u &optional looked-thru)
  ;; TODO - contrast with Examples accessor
  (or (getprop u 'examples)
      (unless (memb u looked-thru)
        (map-union (specializations u)
                   (lambda (su)
                     (gather-examples su looked-thru))))))

(defun define-if-slot (s)
  ;; TODO - comment
  (when (and (slotp s)
             (not (symbol-function s)))
    (push s *slots*)
    (define-slot s))
  s)

;; TODO - this creates the slot reader function, which is just a small part of manifesting a slot. Rename this
(defun define-slot (s)
  ;; ORIG: Really this should doublecheck that s isa slot
  ;; TODO - CCODEP and EXPRP are compiler tests to see if something is compiled. Figure this out later
  ;; TODO - this becomes intrinsically defined in DEFCLASS anyway
  ;; Some of these slots are predefined at toplevel, and should just be compiled (which happens by default in modern code)
  ;; Else, we create a getprop-based slot accessor

  ;; Orig code: (Note that the return value is not used by any caller)
  '(cond
    ((ccodep s) s)
    ((exprp s) (comp s (getd s) t))
    ;; TODO - S is KWOTEd
    ;; Define the function which getprops the named slot
    (t (putd s `(lambda (u) (getprop u ',s)))
       (comp s (getd s))))
  
  ;; CL code:
  (unless (fboundp s)
    (setf (symbol-function s) (lambda (unit)
                                (getprop unit s)))))

(defun kill-slot (s &optional u1 v1)
  (and (slotp s)
       ;; FIX - if U1 wasn't provided, it checked for boundp 'U, which might be a snoop up the call stack?
       ;;  Changed callers to explicitly set this
       (or u1
           (and (boundp 'u)
                (setf u1 u)))
       (prog1 (let (temp)
                (cond
                  ((null (or v1 (setf v1 (funcall s u1))))
                   (list u1 'had 'no s 'slot))
                  ((setf temp (car (inverse s)))
                   (dolist (e v1)
                     (rem1prop e temp u1))
                   '(via inverse))
                  ((setf temp (to-delete s))
                   (funcall temp v1 s u1)
                   '(via to-delete))
                  ((setf temp (to-delete-1 s))
                   (dolist (e v1)
                     (funcall temp e s u1))
                   '(via to-delete-1))
                  (t nil)))
         (remprop u1 s))))

(defun sib-slots (s)
  (map-union (super-slots s) #'sub-slots))

(defun slotp (s)
  (does-intersect '(slot criterial-slot non-criterial-slot)
                  (getprop s 'isa)))

(defun slot-names (u)
  (subset (propnames u)
          (lambda (s)
            (not (memb s *sysprops*)))))

(defun slot-subst (n nold l)
  ;; TODO - mapcar
  (cond
    ((null l) nil)
    (t (cons (car l)
             (cons (subst n nold (cadr l))
                   (slot-subst n nold (cddr l)))))))



;;;;-----------------------------
;;;; Non-default slot readers

(defun alg (u)
  "Search the ALG slot or subslots for a value"
  (or (getprop u 'alg)
      (find-if (lambda (slot)
                 (funcall slot u))
               (sub-slots 'alg))))

(defun defn (u)
  ;; TODO - comment
  (or (getprop u 'defn)
      ;; Probe all the subslots of DEFN to find something
      (find-if (lambda (s)
                 (funcall s u))
               (sub-slots 'defn))
      (and (isa u 'category)
           ;; Defn of a category is an ISA test
           ;; TODO - return a closure, or this source code?
           `(lambda (z)
              (memb ',u (isa z))))))

(defun examples (u &optional looked-thru)
  ;; TODO - comment
  (or (getprop u 'examples)
      (unless (memb u looked-thru)
        (push u looked-thru)
        (map-union (specializations u)
                   (lambda (su)
                     (examples su looked-thru))))))

(defun generalizations (u)
  ;; TODO - comment
  (self-intersect (nconc (mapconc (getprop 'generalizations 'sub-slots)
                             (lambda (ss)
                               (copy-list (getprop u ss))))
                         (getprop u 'generalizations))))

(defun instances (u)
  (cond
    ((memb 'heurisic (isa u)) 'applics)
    ((memb 'op (isa u)) 'applics)
    (t 'examples)))

(defun specializations (u)
  (self-intersect (nconc (mapconc (getprop 'specializations 'sub-slots)
                             (lambda (ss)
                               (append (getprop u ss))))
                         (getprop u 'specializations))))

(defun direct-applics (u)
  ;; TODO - comments
  (subset (applics u)
          (lambda (x)
            ;; TODO - accessor
            (memb (caddr x) '(nil 1)))))

(defun indirect-applics (u)
  (subset (applics u)
          (lambda (a)
            (not (memb (caddr a) '(nil 1))))))

(defun known-applic (u a)
  (car (some (lambda (ap)
               (equal a (car ap)))
             (applics u))))




;;;;------------------
;;;; Slot iterators
;;;;
;;;; These also obey max time/space when working on tasks

(defun map-applics (u f)
  ;; ORIG: This may have to generate examples, rather than merely calling Applics
  (mapc f (applics u))
  (when-let* ((gen (applic-generator u))
              (genf (applic-gen-build gen))
              (gena (applic-gen-args gen))
              ;; TODO - these next 4 were params, but the only call site didn't use them anyway
              (nit 300)
              (when-to-check (1+ (floor nit 10)))
              (max-real-time (* *cur-pri* *user-impatience*
                                ;; TODO - quite a magic calculation
                                (1+ (floor (+ 0.5 (log (max 2 (1+ *verbosity*))))))))
              (max-space (average *cur-pri* 1000)))
    ;; TODO - this length check eliminates an internal loop, but how actually impactful is that? verify that the general 2nd clause will work for everything
    (if (= 1 (length gena))
        (loop initially (set (car gena) (car (applic-gen-init gen)))
              for j from 1 to nit
              until (or (taking-too-long j when-to-check max-real-time)
                        (taking-too-much-space j when-to-check max-space u 'applics))
              do (progn
                   ;; TODO - evil eval
                   (funcall f (eval (car gena)))
                   (set (car gena) (funcall (car genf) (eval (car gena))))))
        (loop initially (mapc #'set gena (applic-gen-init gen))
              for j from 1 to nit
              until (or (taking-too-long j when-to-check max-real-time)
                        (taking-too-much-space j when-to-check max-space u 'applics))
              do (progn
                   (apply-eval f gena)
                   (mapc (lambda (var fn)
                           (set var (apply-eval fn gena)))
                         gena
                         genf))))))

(defun map-examples (u f nit)
  ;; ORIG: This may have to generate examples, rather than merely calling Applics
  (let ((gen (generator u)))
    (if-let ((gen gen) ;; just to have it hit the IF-check
             (genf (gen-build gen))
             (gena (gen-args gen))
             (nit 1000)
             (when-to-check (1+ (floor nit 10)))
             (max-real-time (* *cur-pri* *user-impatience*
                               (1+ (floor (+ 0.5 (log (max 2 (1+ *verbosity*))))))))
             (max-space (average *cur-pri* 500)))
      (if (= 1 (length gena))
          (loop initially (set (car gena) (car (gen-init gen)))
                for j from 1 to nit until (or (taking-too-long j when-to-check max-real-time)
                                              (taking-too-much-space j when-to-check max-space u 'examples))
                do (progn
                     (funcall f (eval (car gena)))
                     (set (car gena) (funcall (car genf) (eval (car gena))))))
          (loop initially (mapc #'set gena (gen-init gen))
                for j from 1 to nit until (or (taking-too-long j when-to-check max-real-time)
                                              (taking-too-much-space j when-to-check max-space u 'examples))
                do (progn
                     (apply-eval f gena)
                     (mapc (lambda (var fn)
                             (set var (apply-eval fn gena)))
                           gena
                           genf))))
      ;; Else
      (mapc f (examples u)))))










;; TODO - could probably combine generalizers & specializers into a more compact form

;;;;----------------
;;;; Generalizers

(defun generalize-1-lisp-expr (bod)
  ;; ORIG - AreUnits is the list of units mentioned in bod; HaveGenl are those which have specializations already
  ;; Plucking values from the COND testing clauses
  (let (tmp tmp2 fbod)
    (cond
      ;; TODO - ugh, what a hairball
      ((setf tmp2 (random-choose
                   (generalizations
                    (setf tmp (random-choose
                               (setf *have-genl*
                                     (union (subset (setf *are-units* (subset (setf fbod (self-intersect (flatten bod)))
                                                                              #'unitp))
                                                    #'generalizations)
                                            *have-genl*)))))))
       (setf *u-diff* (list tmp '-> tmp2))
       (random-subst tmp2 tmp bod))
      ((setf tmp2 (generalize-number (setf tmp (random-choose (subset (self-intersect fbod) #'numberp)))))
       (setf *u-diff* (list tmp '-> tmp2))
       (random-subst tmp2 tmp bod))
      (t bod))))

(defun generalize-1-lisp-fn (bod)
  (generalize-1-lisp-expr bod))

(defun generalize-1-lisp-pred (bod)
  ;; TODO - the original lambda also has tmp & tmp2. Does this create visible bindings that are used?
  (generalize-1-lisp-expr bod))

(defun generalize-bit (b)
  (not b))

(defun generalize-compiled-lisp-code (x)
  ;; I guess we can't do anything about it, if we haven't kept the source?
  x)

(defun generalize-data-type (x)
  (let (tmp)
    (cond
      ((consp x)
       (mapcar (lambda (z)
                 (if (randomp)
                     (generalize-data-type z)
                     z))
               x))
      ((setf tmp (random-choose (generalizations x)))
       (setf *u-diff* (list x '-> tmp))
       tmp)
      (t x))))

(defun generalize-dotted-pair (x)
  x)

(defun generalize-io-pair (x)
  ;; ORIG: eventually:  look thru the (i o) pairs, and make a few new ones, with i's selected from the set of i's, and o's similarly -- or selectionf rom examples of things which i and o are examples of
  x)

(defun generalize-lisp-fn (x)
  ;; ORIG: presumed to be given either the name of a predicate, or a list of the form (LAMBDA --)
  (cond
    ((numberp x) (generalize-number x))
    ((symbolp x) (if-let ((genls (generalizations x)))
                   (caddr (setf *u-diff* (list x '-> (random-choose genls))))
                   x))
    ((not (consp x)) x)
    ((consp (car x)) (mapcar (lambda (z)
                               (if (randomp)
                                   (generalize-lisp-fn z)
                                   z))
                             x))
    ((eq (car x) 'lambda) (cons 'lambda (cons (cadr x)
                                              (mapcar #'generalize-1-lisp-fn (cddr x)))))
    (t x)))

(defun generalize-lisp-pred (x)
  ;; ORIG: presumed to be given either the name of a predicate, or a list of the form (LAMBDA --)
  (cond
    ((numberp x) (generalize-number x))
    ((symbolp x) (if-let ((genls (generalizations x)))
                   (caddr (setf *u-diff* (list x '-> (random-choose genls))))
                   x))
    ((not (consp x)) x)
    ((consp (car x)) (mapcar (lambda (z)
                               (if (randomp)
                                   (generalize-lisp-pred z)
                                   z))
                             x))
    ((eq (car x) 'lambda) (cons 'lambda (cons (cadr x)
                                              (mapcar #'generalize-1-lisp-pred (cddr x)))))
    (t x)))

(defun generalize-list (x)
  (cond
    ((consp (car x)) (mapcar (lambda (z)
                               (if (randomp)
                                   (generalize-list z)
                                   z))
                             x))
    (t (setf *u-diff* '("Duplicated: "))
       ;; Randomly duplicate entries of the list, keeping it sorted?
       (sort (append (subset x (lambda (r)
                                 (if (randomp)
                                     (progn (nconc1 *u-diff* r) nil)
                                     t)))
                     x)
             #'randomp))))

(defun generalize-nil (x)
  (warn "~s can't be generalized if it doesn't have a known DataType!" x))

(defun generalize-number (x)
  (cond
    ;; OPTIMIZATION - which case is most frequent?
    ((consp x) (mapcar (lambda (z)
                         (if (randomp)
                             (generalize-number z)
                             z))
                       x))
    ((fixp x) (caddr (setf *u-diff* (list x '-> (rand x (if (<= x 1000)
                                                            1000
                                                            (* x 10)))))))
    ((numberp x) (caddr (setf *u-diff* (list x '-> (floor (rand (floor (* x 200))
                                                                (floor (* x (max 5.0 x) 200)))
                                                          200.0)))))
    (t nil)))

(defun generalize-slot (x)
  (let (tmp)
    (cond
      ((consp x) (mapcar (lambda (z) (if (randomp)
                                         (generalize-slot z)
                                         z))
                         x))
      ((setf tmp (random-choose (generalizations x)))
       (setf *u-diff* (list x '-> tmp))
       tmp)
      (t x))))

(defun generalize-text (x)
  (cond
    ((consp (car x)) (mapcar (lambda (z) (if (randomp)
                                             (generalize-text z)
                                             z))
                             x))
    (t (setf *u-diff* '("Duplicated: "))
       (sort (append (subset x (lambda (r)
                                 (if (randomp)
                                     (progn (nconc1 *u-diff* r) nil)
                                     t)))
                     x)
             #'randomp))))

(defun generalize-unit (x)
  (let (tmp)
    (cond
      ((consp x) (mapcar (lambda (z)
                           (if (randomp)
                               (generalize-unit z)
                               z))
                         x))
      ((setf tmp (random-choose (generalizations x)))
       (setf *u-diff* (list x '-> tmp))
       tmp)
      (t x))))


;;;;-----------------
;;;; Specializers

(defun specialize-1-lisp-expr (bod)
  ;; ORIG: AreUnits is the list of units mentioned in bod; HaveSpec are those which have specializations already
  (let (tmp tmp2 fbod)
    (cond
      ((setf tmp2 (random-choose
                   (specializations
                    (setf tmp (random-choose
                               (setf *have-spec* (union
                                                  (subset
                                                   (setq *are-units*
                                                         (subset (setf fbod (self-intersect (flatten bod))) #'unitp))
                                                   #'specializations)
                                                  *have-spec*)))))))
       (setf *u-diff* (list tmp '-> tmp2))
       (random-subst tmp2 tmp bod))
      ((setf tmp2 (specialize-number (setf tmp (random-choose (subset (self-intersect fbod) #'numberp)))))
       (setf *u-diff* (list tmp '-> tmp2))
       (random-subst tmp2 tmp bod))
      (t bod))))

(defun specialize-1-lisp-fn (bod)
  (specialize-1-lisp-expr bod))

(defun specialize-1-lisp-pred (bod)
  ;; TODO - orig had 2 extra unused parmaeters: tmp & tmp2
  (specialize-1-lisp-expr bod))

(defun specialize-bit (b)
  (not b))

(defun specialize-compiled-lisp-code (x)
  x)

(defun specialize-data-type (x &aux tmp)
  (cond
    ((consp x)
     (mapcar (lambda (z)
               (if (randomp)
                   (specialize-data-type z)
                   z))
             x))
    ((setf tmp (random-choose (specializations x)))
     (setf *u-diff* (list x '-> tmp))
     tmp)
    (t x)))

(defun specialize-dotted-pair (x)
  x)

(defun sepcialize-io-pair (x)
  ;; ORIG: eventually: look thru the (i o) pairs, and make a few new ones, with i's selected from the set of i's, and o's similarly -- or select from examples of things which I can o are examples of
  x)

(defun specialize-lisp-fn (x)
  (cond
    ((numberp x) (specialize-number x))
    ((symbolp x) (if-let ((specs (specializations x)))
                     (caddr (setf *u-diff* (list x '-> (random-choose specs))))
                     x))
    ((not (consp x)) x)
    ((consp (car x)) (mapcar (lambda (z)
                               (if (randomp)
                                   (specialize-lisp-fn z)
                                   z))
                             x))
    ((eq (car x) 'lambda)
     `(lambda ,(cadr x) ,@ (mapcar #'specialize-1-lisp-fn (cddr x))))
    (t x)))

(defun specialize-lisp-pred (x)
  (cond
    ((numberp x) (specialize-number x))
    ((symbolp x) (if (specializations x)
                     (caddr (setq *u-diff* (list x '-> (random-choose (specializations x)))))
                     x))
    ((not (consp x)) x)
    ((consp (car x)) (mapcar (lambda (z)
                               (if (randomp)
                                   (specialize-lisp-pred z)
                                   z))
                             x))
    ((eq (car x) 'lambda) `(lambda ,(cadr x) ,@(mapcar #'specialize-1-lisp-pred (cddr x))))
    (t x)))

(defun specialize-list (x)
  (cond
    ((consp (car x)) (mapcar (lambda (z)
                               (if (randomp)
                                   (specialize-list z)
                                   z))
                             x))
    (t (setf *u-diff* '("Eliminated: "))
       (subset x (lambda (r)
                   (if (randomp)
                       (progn
                         (nconc1 *u-diff* r)
                         nil)
                       t))))))

(defun specialize-nil (x)
  (warn "~s can't be specialized if it doesn't have a known DataType!" x))

(defun specialize-number (x)
  (cond
    ((consp x) (mapcar (lambda (z)
                         (if (randomp)
                             (specialize-number z)
                             z))
                       x))
    ((fixp x) (caddr (setf *u-diff* (list x '-> (rand 1 x)))))
    ((numberp x) (caddr (setf *u-diff* (list x '-> (floor (rand 0 (floor (* x 200)))
                                                          200.0)))))
    (t nil)))

(defun specialize-slot (x)
  (let (tmp)
    (cond
      ((consp x) (mapcar (lambda (z)
                           (if (randomp)
                               (specialize-slot z)
                               z))
                         x))
      ((setf tmp (random-choose (specializations x)))
       (setf *u-diff* (list x '-> tmp))
       tmp)
      (t x))))

(defun specialize-text (x)
  (cond
    ((consp (car x)) (mapcar (lambda (z)
                               (if (randomp)
                                   (specialize-text z)
                                   z))
                             x))
    (t (setf *u-diff* '("Eliminated: "))
       (subset x (lambda (r)
                   (if (randomp)
                       (progn
                         (nconc1 *u-diff* r)
                         nil)
                       t))))))

(defun specialize-unit (x)
  (let (tmp)
    (cond
      ((consp x) (mapcar (lambda (z)
                           (if (randomp)
                               (specialize-unit z)
                               z))
                         x))
      ((setf tmp (random-choose (specializations x)))
       (setf *u-diff* (list x '-> tmp))
       tmp)
      (t x))))



;;;;-----------------
;;;; Tasks & agenda

(defvar *task-num* 0)

(defvar *task-results*)

(defvar *cur-pri*)

(defun cur-sup (esa)
  ;; TODO - comment, some sort of task field accessor
  (car (cddddr esa)))

(defun cycle-through-agenda ()
  "Run tasks on the agenda, in order from the CAR."
  ;; Since the agenda might change during work, pop each task anew from the var itself.
  (loop for task = (pop *agenda*)
        while task
        do (work-on-task task)))

(defun merge-tasks (l m)
  (prog1 (merge 'list (subset l (lambda (task-to-be-added &aux task-already-there new-reasons)
                                  (cond
                                    ((not (worth-working-on task-to-be-added)) nil)
                                    ((setf task-already-there (whole-task (extract-unit-name task-to-be-added)
                                                                          (extract-slot-name task-to-be-added)
                                                                          (cur-sup task-to-be-added)
                                                                          *agenda*))
                                     (nconc (extract-reasons task-already-there)
                                            (setf new-reasons (set-difference (extract-reasons task-to-be-added)
                                                                             (extract-reasons task-already-there)
                                                                             ;; TODO: :test #'eq ?
                                                                             )))
                                     (cprin1 87 "~%Ha! This task was ALREADY on the agenda: " (wax-on task-to-be-added)
                                             "~%So instead of adding this as a NEW task, we just stick on the reasons " new-reasons
                                             ", and boost the priority to ")
                                     (reset-pri task-already-there
                                                (extract-priority task-to-be-added)
                                                (extract-priority task-already-there)
                                                new-reasons)
                                     (cprin1 87 (extract-priority task-already-there) ".~%")
                                     nil)
                                    (t t))))
                m
                #'order-tasks)
    (snazzy-agenda)))

(defun order-tasks (t1 t2)
  (> (car t1) (car t2)))

(defun add-to-agenda (tasks)
  (setf *agenda* (merge-tasks tasks *agenda*)))

(defun add-task-results (key val)
  (setf *task-results* (add-prop-l *task-results* key val)))

(defun reset-pri (old-t new-p old-p new-r)
  ;; ORIG: Given an old task OldT with priority OldP we have added it anew to the agenda with priority NewP and brand new reasons NewR
  (rplaca old-t (min 1000 (+ (max old-p new-p)
                             (max 10 (* 100 (length new-r)))))))

(defun whole-task (u s sup l)
  ;; ORIG: Find a task on the agenda L which is to work on slot s of unit u
  (car (some (lambda (z)
               (and (eq u (extract-unit-name z))
                    (eq s (extract-slot-name z))
                    (equal (assoc 'slot-to-change sup)
                           (assoc 'slot-to-change (cur-sup z)))))
             l)))

(defun worth-working-on (task)
  (>= (extract-priority task) *min-pri*))


;; TODO - duplicated in original source code?
(defun work-on-task (task)
  (let ((*arg-unit* task)
        (*time-elapsed*)
        (*task-results*))
    (setf *abort-task?* nil)
    (incf *task-num*)
    (cond
      ((> *verbosity* 88)
       (cprin1 88 "~%Task " *task-num* ": Working on the promising task " task "~%"))
      ((> *verbosity* 10)
       (cprin1 1 "~%Task " *task-num* "~%")))
    (setf *cur-pri* (extract-priority task))
    (setf *cur-unit* (extract-unit-name task))
    (setf *cur-slot* (extract-slot-name task))
    ;; TODO *old-val* is never read. However, there i an *old-value* but that's probably different?
    (setf *cur-val* (setf *old-val* (funcall *cur-slot* *cur-unit*)))
    (setf *new-values* nil)
    (setf *cur-reasons* (extract-reasons task))
    (setf *cur-sup* (cur-sup task))
    (when (is-alto)
      (snazzy-task)
      (snazzy-agenda)
      (snazzy-concept t))
    (or (every (lambda (p)
                 (setf *heuristic-agenda* (examples 'heuristic))
                 (loop for r = (pop *heuristic-agenda*)
                       unless r return t
                         when *abort-task?* return nil
                           do (cond
                                ((null (funcall p r)))
                                ((subsumed-by r))
                                ((case (funcall (funcall p r) task)
                                   ;; TODO - there is no NAborts in the code? how is the slot/accessor generated?
                                   ;; TODO - HAvoid and HAvoidIfWorking set AbortTask to 'AbortTask!, but this code just checked for the literal value AbortTask so I don't know what ever triggers this case?
                                   (abort-task (put r 'num-aborts
                                                    (1+ (or (num-aborts r) 0)))
                                    (return nil))
                                   (nil nil)
                                   (otherwise
                                    (and (cprin1 66 "  The " p " slot of heuristic " r " " (abbrev r)
                                                 " applies to the current task.~%")
                                         (or (and (is-alto)
                                                  (snazzy-heuristic r p))
                                             t)
                                         (my-time '(every #'xeq-if-it-exists (sub-slots 'then-parts))
                                                  '*time-elapsed*)
                                         (or (and (is-alto)
                                                  (snazzy-concept t))
                                             t)
                                         (cprin1 68 "       The Then Parts of the rule have been executed.~%~%")
                                         (setf *tim-rec* (or (overall-record r)
                                                             (put r 'overall-record (cons 0 0))))
                                         (incf (cdr *tim-rec*))
                                         (incf (car *tim-rec*) *time-elapsed*))))))
                       ))
               (sub-slots 'if-task-parts))
        (add-task-results 'termination 'aborted))
    (cprin1 64 " The results of this task were: " *task-results* "~%")
    (cprin1 65 "~%")
    *task-results*))

;; TODO - duplicated work-on-unit

(defun work-on-unit (u)
  (let (*task-results*)
    (incf *task-num*)
    (when (is-alto)
      (snazzy-task (list (worth u)
                         u
                         'any
                         `("There are no great tasks on the Agenda now"
                           (,u "has the highest Worth of any concept I haven't focused on recently"))))
      (snazzy-concept t u))
    (cprin1 10 "~%Task " *task-num* ": Focusing on " u "~%")
    (dolist (h (examples 'heuristic))
      ;; ORIG: try to apply H to unit U
      (funcall *interp* h u))
    (cprin1 65 "~%")
    (when *task-results*
      (cprin1 64 " The results of this task so far are: " *task-results* "~%"))
    (cprin1 65 "~%")
    (and (is-alto)
         (snazzy-heuristic nil))
    (cycle-through-agenda)
    u))






;;;;-----------------
;;;; Interpreters

(defun rule-taking-too-long ()
  ;; TODO - (clock 0) is time of day in milliseconds
  (or (and (> (clock 0) *max-rule-time*)
           (cprin1 51 " Hmmm...   this rule is taking too long!  On to better rules!~%")
           t)
      (and (> (count (getprop *cur-unit* *cur-slot*))
              *max-rule-space*)
           (cprin1 51 " Grumble...   this rule is taking too much space!  On to less expansive rules!~%")
           t)))

;; TODO - these are repetitive with their RULE-TAKING-TOO-* counterparts
(defun taking-too-long (j when-to-check max-real-time)
  (cond
    ((< j 1)
     (setq *map-cycle-time* (clock 0))
     nil)
    ((and (eq 0 (rem j when-to-check))
          (>= (- (clock 0) *map-cycle-time*)
              max-real-time))
     (cprin1 56 " Hmm...   this is taking too long!  On to better things!~%")
     t)
    (t nil)))

(defun taking-too-much-space (j when-to-check max-space u s)
  (cond
    ((<= j 1) nil)
    ((and (eq 0 (rem j when-to-check))
          (>= (count (getprop u s))
              max-space)
          (cprin1 56 " Grumble...   this is taking too much space!  On to less expansive rules!~%")
          t))
    (t nil)))



(defun run-alg (f &rest args)
  (let ((val (cond
               ((alg f) (apply (alg f) args))
               ((symbol-function f) (apply f args))
               (t nil))))
    (accumulate-rarity f (not (eq val 'failed)))
    val))

(defun run-defn (f &rest args)
  (let ((val (cond
               ((defn f) (apply (defn f) args))
               ((symbol-function f) (eval (cons f args)))
               (t nil))))
    (accumulate-rarity f (not (eq val 'failed)))
    val))

(defun accumulate-rarity (unit success?)
  (let ((rarity (rarity unit)))
    (if success?
        (incf (second rarity))
        (incf (third rarity)))
    ;; Rarity = num-successes / total-calls
    (setf (first rarity) (floor (float (second rarity))
                                (+ (second rarity)
                                   (third rarity))))))



(defun interp1 (r *arg-unit*)
  (declare (ignore r))
  ;; ORIG: assembles pieces of the heuristic rule r, and runs them on argument ArgU.
  (every #'true-if-it-exists (sub-slots 'if-parts)))

(defun interp2 (r *arg-unit*)
  ;; ORIG: assembles pieces of the heuristic rule R, and runs them on argument ArgU.
  ;; ORIG: This is a more "vocal" interpreter than interp1
  (cond
    ((every #'true-if-it-exists (sub-slots 'if-parts))
     (and (is-alto)
          (snazzy-heuristic r))
     (cprin1 66 "    All the IfParts of " r " " (abbrev r) " are satisfied, so we are applying the ThenParts.~%")
     (cprin1 29 r " applies.~%")
     (and (my-time '(every #'xeq-if-it-exists (subslots 'then-parts))
                   '*time-elapsed*)
          (cprin1 68 "~%  All the ThenParts of " r " " (abbrev r) " have been successfully executed.~%")
          (setf *tim-rec* (or (overall-record r)
                              (put r 'overall-record (cons 0 0))))
          (incf (cdr *tim-rec*))
          (incf (car *tim-rec*) *time-elapsed*)
          t))))

;; TODO - interp2 was exactly duplicated back-to-back in EUR, I don't think that changes anything?

(defun interp3 (r *arg-unit* *arg-slot*)
  ;; ORIG: assembles pieces of the heuristic rule r, and runs them on argument ArgU and slot ArgS
  ;; ORIG: This is a more "vocal" interpreter than interp1
  (let ((*cur-unit* *arg-unit*)
        (*cur-slot* *arg-slot*))
    (cond
      ((every #'true-if-it-exists (sub-slots 'if-parts))
       ;; The COND ensures that only 1 option will be printed, not both if the verbosity is high
       (cond
         ((> *verbosity* 66) (cprin1 66 " All the IfParts of " r " " (abbrev r) " are satisfied, so we are applying the ThenParts.~%"))
         ((> *verbosity* 29) (cprin1 29 r " applies.~%")))
       (and (my-time '(every #'xeq-if-it-exists (sub-slots 'then-parts))
                     '*time-elapsed*)
            (cprin1 68 "~%       All the ThenParts of " r " " (abbrev r) " have been successfully executed.~%")
            (setf *tim-rec* (or (overall-record r)
                                (put r 'overall-record (cons 0 0))))
            (incf (cdr *tim-rec*))
            (incf (car *tim-rec*) *time-elapsed*)
            t)))))

;; TODO - what is R?
(defun true-if-it-exists (s)
  ;; ORIG: This is an aux fn of rule interpreters. We assume that the interpreter is being run on a rule called r, which is to be applied to a unit ArgU
  (let ((z (funcall s r)))
    (cond
      ((null z))
      ((< *verbosity* 80)
       (funcall z *arg-unit*))
      ((funcall z *arg-unit*)
       (cprin1 -1 "        the " s " slot of " r " holds for " *arg-unit* "~%")
       t)
      ((> *verbosity* 95)
       (cprin1 95 "        the " s " slot of " r " didn't hold for " *arg-unit* "~%")
       nil))))

(defun xeq-if-it-exists (s)
  ;; ORIG: This is an aux fn of rule interpreters. We assume that the interpreter is being run on a rule called r, which is to be applied to a unit ArgU
  ;; ORIG: This function evaluates the s part of r, which is presumably a Then- part of some sort
  (let ((z (funcall s r))
        (*time-elapsed*)
        (*tim-rec*))
    (cond
      ((null z) t)
      ((my-time '(funcall z *arg-unit*)
                '*time-elapsed*)
       (cprin1 80 "        the " s " slot of " r " has been applied successfully to " *arg-unit* "~%")
       (setf *tim-rec* (or (funcall (car (record s)) r)
                           (put r (car (record s)) (cons 0 0))))
       (incf (cdr *tim-rec*))
       (incf (car *tim-rec*) *time-elapsed*)
       (cprin1 75 "        the " s " slot or " r " was applied to " *arg-unit*
               ", but for some reason it signalled a failure.~%")))))




;;;;------------------------------
;;;; Code & Execution utilities

(defun apply-eval (funcname argl)
  "Evaluate the literal args, then call the given function name"
  (eval (cons funcname argl)))

(defun comp (funcname def &optional save-expr?)
  "Compile a function, and delete the source code from the unit if requested."
  (compile funcname def)
  (unless save-expr?
    (remprop funcname 'expr)))

(defvar *time-elapsed*)

(defun my-time (ex &optional (var '*time-elapsed*))
  (cprin1 0 "setting variable " var "~%")
  (set var
       ;; TODO - (clock 2) is compute/busy time not including GC, since start of the lisp environment
       (let ((start (clock 2)))
         (eval ex)
         (- (clock 2) start))))









;;;;---------------
;;;; Environment

(defun interrupts ()
  ;; TODO - we can use threads to throw a function evaluation at the running thread to execute these
  ;; ORIG: Control L for agenda length; Control N for number of newly synthesized units
  ;; Interrupt char 12
  '(cprin1 -2 "~%    Agenda length = " (length *agenda*) "~%~%")
  ;; Interrupt char 14
  '(cprin1 -2 "~%    " (length *new-u*) " newly synthesized units~%~%")
  ;; Interrupt char 22
  '(progn
    (cprin1 -2 "~%~%    Verbosity level was " *verbosity* "; new value: ")
    (let ((r (read)))
      (and (fixp r)
           (setf *verbosity* r)))))

(defun is-alto ()
  ;; (eq 'alto (systemtype))
  nil)

(defun clock (type)
  (ecase type
    (0 ;; Current wall-time milliseconds, since lisp startup
     (floor (get-internal-real-time) (floor internal-time-units-per-second 1000)))
    (2 ;; Compute time not including GC, since lisp startup
     (floor (get-internal-run-time) (floor internal-time-units-per-second 1000)))))



;;;;--------
;;;; Main


(defmacro eu (&rest args)
  ;; NLAMBDA stump to have unevaluated args
  `(%eu-impl ',args))

(defun %eu-impl (*editpx*)
  (when (cond
          ((unitp (car *editpx*))
           (setf *last-edited* *editpx*))
          (*editpx*
           (cprin1 0 "EU complaining:  not an existing unit name!~%What did you really mean to type?  ")
           (eu (read))
           nil)
          ;; Here *editpx* is nil, we didn't give it any args so it uses last-edited
          ((setf *editpx* *last-edited*)
           (cprin1 0 "=" (car *editpx*) "~%")
           t))
    (let* ((unit (car *editpx*))
           (proplist (getproplist unit)))
      (setf *editp-temp* (copy proplist))
      (map-plist proplist #'check-after-editp)
      (map-plist *editp-temp* #'check-2-after-editp)
      ;; finished-editing is probably output display, and not referring to any function name
      (cons 'finished-editing *editpx*))))

(defun eurisko (&optional verbosity eternal-flag)
  (when (fixp verbosity)
    (setf *verbosity* verbosity))
  (format t "~%~%~%                             Starting EURISKO~%~%~%~%Douglas B. Lenat~%February, 1981~%~%")
  (format t "~%~%Common Lisp port by White Flame, 2023-2024~%~%")
  (initialize-eurisko)
  (setf *task-num* 0)
  (cprin1 -1 "~%Ready to start? ")
  (cond
    ((yes-no) (start eternal-flag))
    (t "Type (START) when you are ready.")))

(defun initialize-eurisko (&optional doit)
  (interrupts)
  (cond
    ((or doit (yes-no nil "Fully Initialize? "))
     (prin1 "OK, defining Slots, UsedSlots, UnusedSlots, NUnitSlots as I go along... ")
     (setf *agenda* nil)
     (setf *conjectures* nil)
     (setf *unused-slots* nil)
     (setf *used-slots* nil)
     (format t "Units~%")
     (dolist (u *units*)
       (format t "Unit ~s~%" u)
       (dolist (sl (propnames u))
         (or (memb sl *used-slots*)
             (memb sl *sysprops*)
             (progn
               (push sl *used-slots*)
               (format t "Defining slot ~s~%" sl)
               (define-slot sl)))))
     (format t "Units2~%")
     (dolist (u *units*)
       (when (and (memb 'slot (isa u))
                  (not (memb u *used-slots*)))
         (push u *unused-slots*)
         (define-slot u)))
     ;; TODO - lots of assumptions that the slots list are of symbols, which can be default sorted by name
     (setf *used-slots* (sort *used-slots* #'default-sort))
     (setf *unused-slots* (sort *unused-slots* #'default-sort))
     (format t "unused-slots~%")
     (mapc #'define-slot *unused-slots*)
     (prin1 "Done! ")
     (cprin1 0 (length (setf *slots* (merge 'list
                                            (copy-list *used-slots*)
                                            (copy-list *unused-slots*)
                                            #'default-sort)))
             " slots")
     (and (setf *n-unit-slots* (subset *slots* #'n-unitp))
          (yes-no nil (format nil "Regarding ~s~%~a slots aren't defined as units.  Do that now? "
                              *n-unit-slots*(length *n-unit-slots*)))
          (dolist (z (copy-list *n-unit-slots*))
            (format t "~%~s" z)
            (new-unit z 'abbrev)
            (setf *n-unit-slots* (delete z *n-unit-slots* :test #'eq))))
     (and *new-u* (cprin1 -1 "~%Eliminate the recently synthesized units? ")
          (cprin1 20 *new-u*)
          (yes-no)
          (map-and-print (copy *new-u*) #'kill-unit))
     (and (some-uneliminated)
          (cprin1 -1 "~%Eliminate the individual values filled in during an earlier run, for slots of units still in existience? ")
          (yes-no)
          (mapc #'initial-elim-slots *units*)))
    (t (cprin1 -1 " OK, just initializing the slot definitions. ~%")
       (dolist (u *units*)
         (dolist (sl (propnames u))
           (or (memb sl *sysprops*)
               (define-slot sl))))
       (dolist (u *units*)
         (and (memb 'slot (isa u))
              (define-slot u)))))
  ;; TODO - synth-u starts populated in this codebase, and isn't rescanned in this initialization:
  ;;  h19-criterial, h5-criterial, h5-good, h-avoid-2-and h-avoid-3-first
  (cprin1 20 "~%There are " (length *units*) " units, of which " (length *synth-u*) " were synthesized by Eurisko.~%")
  (cprin1 21 "Of those, ~%")
  (report-on '(heuristic math-op math-obj repr-concept) 21)
  (cprin1 20 "~%")
  '!)

(defun start (&optional eternal-flag)
  (cycle-through-agenda)
  (let ((units-focused-on nil)
        (uu nil))
    (loop do (progn
               (cond
                 ((setf uu (set-diff *units* units-focused-on)))
                 (eternal-flag (cprin1 3 "~%~%~%Have focused on all the units at least once.  Starting another pass through them.~%~%~%")
                               (setf units-focused-on nil))
                 (t (prin1 "~%Should I continue with another pass? ")
                    (or (yes-no)
                        (return 'eurisko-halting))
                    (setf units-focused-on nil)))
               (setf units-focused-on (cons (work-on-unit (maximum uu #'worth))
                                            units-focused-on))
               (and (is-alto)
                    (null *agenda*)
                    ;;(DSPRESET BitAgenda)
                    (cprin1 (length uu) " concepts still must be focused on sometime"))))))







;;;;--------------------------
;;;; TUI input & output

(defun yes-no (&optional i prompt)
  (when (and prompt (null i))
    (cprin1 -1 "~%" prompt " (Y or N): "))
  (memb (or i (read))
        '(y yes)))

(defun cprin1 (verbosity &rest args)
  "Prints all arguments to the console, if *VERBOSITY* is high enough to include it."
  (when (> *verbosity* verbosity)
    (dolist (arg args)
      (if (stringp arg)
          ;; Interpret zero-parameter format strings
          (format t arg)
          ;; Normal object print
          (prin1 arg))))
  t)

(defun percentify (n)
  (format nil "~a%" (floor (* 100 (+ n 0.005)))))

(defun date2 ()
  "Returns a current month+day string"
  ;; TODO - takes return from (DATE) which is a string like "14-MAY-71 14:26:08", and returns "MAY14"?
  ;; only used in the dribble output filename?
  (multiple-value-bind (sec min hour date month) (get-decoded-time)
    (declare (ignore sec min hour))
    (format nil "~a~2,'0d" (aref #(jan feb mar apr may jun jul aug sep oct nov dec) (1- month)) date)))

;; TODO - much of this printing stuff uses PRINDEN, which is defined in P[AM,DBL], and is alto GUI stuff for an indented print

(defun prinbol (s v)
  ;; ORIG: This prints s : (in bold) and then v (indented)
  ;; TODO - maybe some clim printing stuff, but keeping this basic for now
  (cprin1 -1 "[" s "]:" v "~%"))

(defun printask (z)
  (cprin1 -1 (extract-priority z) " " (extract-unit-name z) " " (extract-slot-name z))
  (dolist (s (cur-sup z))
    (case (car s)
      ((slot-to-use slot-to-change)
       (cprin1 -1 " " (car s) "=" (if (null (cddr s)) (cadr s) (cdr s))))
      (otherwise
       (cprin1 -1 "..."))))
  (cprin1 -1 "~%    " (length (extract-reasons z)) " Reasons~%"))

(defun pu (u ns)
  ;; TODO - print unit?
  (when (numberp u)
    (setf u (car (nth *new-u* u))))
  (cprin1 -1 "~%:~%~%")
  (loop for pl in (getproplist u) by #'cddr
        do (if (slotp (car pl))
               (progn
                 (cprin1 -1 (car pl) ": ")
                 (printdef (cadr pl))
                 (cprin1 -1 "~%"))
               (push (car pl) ns)))
  (when ns
    (cprin1 -1 "~%Plus " (length ns) " properties which are not slot names: " ns "~%~%"))
  u)

(defun pu2 (u f ns sn)
  (declare (ignore f))
  (when (numberp u)
    (setf u (car (nth *new-u* u))))
  ;; TODO - more bold & layout stuff in the original
  (cprin1 -1 "[" u "]:")
  (dolist (s (propnames u))
    (if (unitp s)
        (push s sn)
        (push s ns)))
  (when (boundp '*cur-slot*)
    (cprin1 -1 "[" *cur-slot* "]: " (getprop u *cur-slot*) "~%")
    (setf sn (delete *cur-slot* sn)))
  (dolist (s (copy-list sn))
    (when (eq 'text (data-type s))
      (cprin1 -1 "[" s "]: " (getprop u s) "~%")
      (setf sn (delete s sn))))
  (dolist (s (copy-list sn))
    (when (atom (getprop u s))
      (cprin1 -1 "[" s "]: " (getprop u s) "~%")
      (setf sn (delete s sn))))
  (dolist (s (copy-list sn))
    (when (and (every #'atom (getprop u s))
               (or (not (atom (cdr (getprop u s))))
                   (null (cdr (getprop u s)))))
      (cprin1 -1 "[" s "]: ")
      (case (length (getprop u s))
        ((0 1 2 3 4 5 6 7 8) (cprin1 -1 (getprop u s)))
        (otherwise
         (prin1 "(")
         (mapc (lambda (k x)
                 (declare (ignore k))
                 (cprin1 -1 x " "))
               '(1 2 3 4 5)
               (getprop u s))
         (cprin1 -1 "+" (- (length (getprop u s)) 5) " more)")))
      (cprin1 -1 "~%")
      (setf sn (delete s sn))))
  (dolist (s (copy-list sn))
    (when (every #'atom (getprop u s))
      (cprin1 -1 "[" s "]: ")
      (case (length (getprop u s))
        ((0 1 2 3 4 5 6 7 8) (cprin1 -1 (getprop u s)))
        (otherwise
         (prin1 "(")
         (mapc (lambda (k x)
                 (declare (ignore k))
                 (cprin1 -1 x " "))
               '(1 2 3 4 5)
               (getprop u s))
         (cprin1 -1 "+" (- (length (getprop u s)) 5) " more)")))
      (cprin1 -1 "~%")
      (setf sn (delete s sn))))
  (when sn
    (cprin1 -1 "~%Plus " (length sn) "big slots: " sn "~%"))
  (when ns
    (cprin1 -1 "~%Plus " (length ns) "properties which are not slot names: " ns "~%"))
  (cprin1 -1 "~%")
  u)

(defun report-on (l n)
  (cond
    ((symbolp l) (setf l (list l)))
    ((not (consp l)) (setf l nil)))
  (dolist (u l)
    (cprin1 n " there are " (length (gather-examples u)) " "
            u "s" " "
            (cond
              ((eq u 'repr-concept)
               `(,(length *slots*) "of which are kinds of slots"))
              (t " "))
            "~%")))

(defun wax-on (task)
  `("It is " ,(certainty (car task)) " that finding " ,(caddr task) " of " ,(cadr task)
             "  will be worthwhile, since: "
             ,(let ((re (cadddr task)))
                (cond
                  ((null re) "no good reason")
                  ((> (length re) 8)
                   `(,(car re) " and " ,(1- (length re)) " other reasons"))
                  (t re)))))


;;;;-----------------
;;;; GUI display

(defun snazzy-agenda ()
  (warn "GUI not implemented"))

(defun snazzy-concept (flag &optional c)
  (declare (ignore flag c))
  (warn "GUI not implemented"))

(defun snazzy-heuristic (&optional h s)
  (declare (ignore h s))
  (warn "GUI not implemented"))

(defun snazzy-task (&optional task)
  (declare (ignore task))
  (warn "GUI not implemented"))




;;;;----------------------------------------
;;;; TODO - Unclassified Eurisko functions

;; TODO - can this be a dynamic binding instead?
(defvar *arg-unit* nil
  "Stored argument carried across functions")

;; TODO - some of these might be replacable by local variables
(defvar *cur-unit*)
(defvar *cur-slot*)
(defvar *cur-val*)
(defvar *cur-reasons*)
(defvar *cur-sup*) ;; set to (cur-sup curent-task)
(defvar *new-values*)
(defvar *tim-rec*)
(defvar *warn-slots*)
(defvar *have-spec*)
(defvar *abort-task?*)
(defvar *old-val*) ;; TODO - written once, no reads
(defvar *heuristic-agenda*)
(defvar *map-cycle-time*)
(defvar *arg-slot*)
(defvar *space-to-use*)

;; These are set by H11, but are the values never read outside of that?  there's no initial/default value anywhere
(defvar *max-rule-time*)
(defvar *max-rule-space*)






(declaim (inline applic-args applic-gen-args applic-gen-build applic-gen-init))
(defun applic-args (x) (car x))
(defun applic-gen-args (x) (caddr x))
(defun applic-gen-build (x) (cadr x))
(defun applic-gen-init (x) (car x))

(defun extract-input (x) (car x))
(defun extract-output (x) (cadr x))
(defun extract-priority (esa) (car esa))
(defun extract-reasons (esa) (cadddr esa))
(defun extract-slot-name (esa) (caddr esa))
(defun extract-unit-name (task) (cadr task))

(defun gen-args (x) (caddr x))
(defun gen-build (x) (cadr x))
(defun gen-init (x) (car x))









(defun check-2-after-editp (old-prop old-val)
  ;; TODO - comment
  (when-let ((inv (inverse old-prop)))
    (when (not (funcall old-prop (car *editpx*)))
      (let ((invprop (car inv)))
        (dolist (e old-val)
          (rem1prop e invprop (car *editpx*)))))))

(defvar *editp-temp* nil
  "Used to pass sideband data through to check-after-editp")

(defun check-after-editp (prop val)
  ;; TODO - comment
  (when-let ((invprop (car (inverse prop))))
    (let ((old (listget *editp-temp* prop)))
      (dolist (e (set-diff val old))
        (dwim-union-prop e invprop (car *editpx*)))
      (dolist (e (set-diff old val))
        (rem1prop e invprop (car *editpx*))))))

(defun check-elim ()
  "Ask the user if generated unit slots should be eliminated"
  (when (yes-no nil "Should I eliminate recently-computed values? ")
    (mapc #'initial-elim-slots *units*)))

(defun check-the-values (u s v)
  "ORIG: doublecheck that all the values on V are legitimate entries for the S slot of U."
  ;; NOTE - empty in the original EUR as well
  ;; TODO - what happens if we instantiate this check?
  (declare (ignore u s v))
  t)








;; TODO - Credit stuff is written to in heuristics, but never read?
(defvar *g-credit*)

(defun decrement-credit-assignment ()
  ;; TODO - comment
  (incf *g-credit*))

(defun initialize-credit-assignment ()
  (setf *g-credit* 1))








;; TODO - comments
(defvar *editpx*) ;; parameters to EU functino
(defvar *last-edited*) ;; 








(defvar *have-genl* nil
  "Units from generalize-1-lisp-expr which already have generalizations")
(defvar *are-units* nil
  "List of units mentioned in the body of generalize-1-lisp-expr")







(defun initial-check-inv (uns)
  (let ((bogus-u nil))
    (and (yes-no nil "Shall I ferret out non-units referred to by honest, true units? ")
         (map-and-print (cond
                          ((null uns) *units*)
                          ((symbolp uns) (list uns))
                          ((consp uns) uns)
                          (t nil))
                        (lambda (un)
                          (let ((must-rem nil))
                            (map-plist (getproplist un)
                                       (lambda (pr val)
                                         (when-let ((inv (car (inverse pr))))
                                           (mapc (lambda (e)
                                                   (or (unitp e)
                                                       (not (symbolp e))
                                                       (not (find #\- (symbol-name e)))
                                                       (progn
                                                         (cprin1 2 "~%" e " mentioned by " un)
                                                         (push (list un pr e) must-rem)
                                                         (push e bogus-u))))
                                                 val))))
                            (dolist (l must-rem)
                              (apply #'rem1prop l)))
                          un)))
    (cprin1 -2 "~%Finished ferreting out non-units. Ready to add all inverse pointers? ")
    (and (yes-no)
         (map-and-print *units* #'add-inv))
    (cprin1 -2 "~%OK.  Do you want me to zero out all the time/calling records of all the heuristics?")
    (and (yes-no)
         (map-and-print (examples 'heuristic)
                        #'zero-records))))

(defun initial-elim-slots (u)
  (dolist (s *slots-to-elim-initially*)
    (remprop u s))
  (dolist (s (elim-slots u))
    (remprop u s)))





;; only used once, in structure interestingness calculation
(defun ok-bin-preds (u)
  (cond
    ((eq u *old-kb-pu*) *old-kb-pv*)
    (t (setf *old-kb-pu* u)
       (setf *old-kb-pv* (subset (examples 'binary-pred)
                                 (lambda (bp)
                                   (and (or (has-high-worth bp)
                                            (memb bp (int-examples 'binary-pred)))
                                        (leq-nn (car (rarity bp))
                                                0.3)
                                        (every #'defn (domain bp))
                                        (run-defn (car (domain bp)) u))))))))

(defun sos ()
  (warn "SOS not implemented"))


;; PACK* is a builtin in IL, Eurisko overwrote it with SmartPack*, saving the old one in OldPack*,
;; which is just the last line of this function
(defun pack* (&rest u)
  (if (>= (loop for ti in u sum (length (if (symbolp ti) (symbol-name ti) ti)))
            100)
      ;; Total characters in all parameters > 100
      (let ((shorter-name (smart-pack* (mapcar #'shorten u))))
        (case (floor *verbosity* 20)
          (0 t)
          (1 (cprin1 0 "    Oh, those long names!  I just had to shorten one.~%"))
          ((2 3 4)
           (cprin1 0 "~%Oh, those long names!!!  I will have to shorten one to " shorter-name "~%"))
          (otherwise
           (cprin1 20 "~%Oh,t hose long names!!!  I will have to shorten "
                   (format nil "~{~a~}" u) " to " shorter-name "~%")))
        ;; FIX - Added this return value. Originally shorter-name was set globally, but nothing read it
        shorter-name)
      ;; Normal packing
      (apply #'symbolicate u)))

(defun shorten (a)
  "Returns a symbol of just the first letter of the given symbol"
  (symbolicate (aref (symbol-name a) 0)))








;; TODO - this is never called in code, nor is it in any other saildart file, so it must be for interactive use. I believe it converts a slot proplist accessor function into calling the slot name itself.
'(defun un-get (flag)
  ;; ORIG: One can call this on units by saying, say, (un-get (mapcar *units* 'getproplist))
  (dolist (f (cond
               ((consp flag) flag)
               ((null flag) (or *gfns* *eurfns*))
               ((symbolp flag) (list flag))
               (t nil)))
    (mapc #'dreplace-get (let ((tmp (lists-starting 'getprop (cond
                                                               ((ccodep f)
                                                                (strong-unsave-def f)
                                                                (getd f))
                                                               ((getd f))
                                                               ((consp f) f)
                                                               (t (warn "In the process of UN-GETting, found a function which was not an EXPR or SUBR!"))))))
                           (when tmp
                             (let ((ff (cond
                                         ((symbolp f) f)
                                         ((car (some (lambda (u)
                                                       (eq f (getproplist u)))
                                                     *units*)))
                                         (t nil))))
                               (when (symbolp f)
                                 (MARKASCHANGED f))
                               (when ff
                                 (cprin1 20 ff " ")
                                 (cprin1 40 "(" (length tmp) " changes.);   "))))
                           tmp))))

;; only called from un-get
'(defun dreplace-get (l)
  "Mutates a slot accessor from a GETPROP expression to a direct function call."
  (cond
    ((quoted (caddr l))
     ;; (getprop sym 'slotname-literal) => (slotname-literal)
     (rplaca l (cadr (caddr l)))
     (rplacd (cdr l) nil)
     l)
    ;; (getprop sym slotname-expr) => (funcall slotname-expr)
    (t (rplaca l (caddr l))
       (rplacd (cdr l) nil)
       (attach 'funcall l))))

;; only called from un-get
'(defun strong-unsave-def (f)
  (cond
    ((eq 'nothing (car (unsavedef f)))
     (car (loaddef f)))
    (t f)))

;; Only called from dreplace-get
'(defun quoted (x)
  (and (consp x)
       (eq (car x) 'quote)))





;; TODO - nothing directly calls or names this, and I don't think there's any PACK* construction for this shape? Probably incomplete.  (cons (l L1) v) is nonsensical and wouldn't build
'(defun some-o-pair (l rel &aux v)
  (cond
    ((< (length l) 2) nil)
    ((some (lambda (l2)
             (and (setf v (apply rel (car l) l2))
                  (setf v (list l2 v))))
           (cdr l))
     ;; TODO - L1 must be an upstream var in the call chain? No, it doesn't exist anywhere else in EUR
     ;; TODO - L is a variable, which must hold a list. this isn't a lisp-1, is it?
     (cons (l l1) v))
    (t (some-pair (cdr l) rel))))

'(defun some-pair (l rel)
  (or (some-o-pair l rel)
      (some-o-pair (reverse l) rel)))



















;;;;-----------------------------
;;;; Units and their properties
;;;;
;;;; Heuristics are Units as well, but broken off into their own section

;; Many of these collection fields are machine-generated from RLL, and should be removed from the source (but use these lists to verify the generated versions). Worth 500 is likely default, don't need to specify those.

;; Rarity is maintained by run-alg or run-defn, so the values in the putprops are likely the runtime accumulated state saved from RLL. The decimal values are too long to be hand-tweaked


(defvar *units* '(int-applics mult-ele-struc-insert h29 h28 h27 h26 h25 rarity why-int h24 h23 is-a-int
                  int-examples less-interesting more-interesting h22 interestingness restrictions
                  extensions op-cat-by-n-args pred-cat-by-n-args tertiary-pred unary-pred binary-pred
                  higher-arity lower-arity non-empty-struc empty-struc set-of-sets
                  structure-of-structures truth-value atom implies not logic-op relation
                  set-of-o-pairs invert-op inverted-op restrict identity1 proj-3-of-3 proj-2-of-3
                  proj-1-of-3 proj-2 proj-1 memb member all-but-last last-ele all-but-third all-but-second
                  all-but-first third-ele second-ele first-ele reverse-o-pair pair o-pair
                  parallel-join-2 parallel-join repeat2 tertiary-op repeat binary-op
                  parallel-replace-2 each-element-is-a unary-op type-of-structure parallel-replace
                  coalesce bag-difference o-set-difference list-difference set-difference
                  struc-difference bag-union list-union o-set-union struc-union bag-intersect
                  o-set-intersect list-intersect struc-intersect set-union set-intersect ord-struc-op
                  ord-struc-equal bag-equal list-equal o-set-equal suf-defn nec-defn un-ord-struc
                  ord-struc no-mult-ele-struc o-set-delete o-set-op o-set-insert o-set
                  mult-ele-struc-delete-1 mult-ele-struc-op mult-ele-struc bag-delete-1 bag-delete bag-op
                  bag-insert bag list-delete-1 list-delete list list-insert list-op set-delete
                  set-insert struc-delete struc-op struc-insert and abbrev add alg always-nil
                  always-nil-2 always-t always-t-2 anything applic-generator applics arity
                  best-choose best-subset bit category compiled-defn compose conjecture
                  conjecture-about conjectures constant-binary-pred constant-pred
                  constant-unary-pred creditors criterial-slot data-type defn direct-applics
                  divisors-of domain dont-copy double-check eq equal elim-slots english even-num
                  examples failed-record failed-record-for fast-alg fast-defn format
                  generalizations generator good-choose good-subset h1 h10 h11 h12 h13 h14 h15
                  h16 h17 h18 h19 h19-criterial h2 h20 h21 h3 h4 h5 h5-criterial h5-good h6 h7 h8
                  h9 h-avoid h-avoid-2 h-avoid-2-and h-avoid-3 h-avoid-3-first h-avoid-if-working heuristic
                  hind-sight-rule ieqp igeq igreaterp ileq ilessp if-about-to-work-on-task
                  if-finished-working-on-task if-parts if-potentially-relevant if-task-parts
                  if-truly-relevant if-working-on-task in-domain-of indirect-applics inverse isa
                  is-range-of iterative-alg iterative-defn math-concept math-obj math-op math-pred
                  multiply nnumber non-criterial-slot non-examples num-op or odd-num op
                  overall-record perf-num perf-square pred prime-num proto-conjec random-choose
                  random-subset range record record-for record-slot recursive-alg recursive-defn
                  repr-concept set set-equal set-of-numbers set-op sib-slots slot specializations
                  square struc-equal structure sub-slots subsetp subsumed-by subsumes successor
                  super-slots task the-first-of the-second-of then-add-to-agenda
                  then-add-to-agenda-failed-record then-add-to-agenda-record then-compute
                  then-compute-failed-record then-compute-record then-conjecture
                  then-conjecture-failed-record then-conjecture-record then-define-new-concepts
                  then-define-new-concepts-failed-rcord then-define-new-concepts-record
                  then-delete-old-concepts then-delete-old-concepts-failed-record
                  then-delete-old-concepts-record then-modify-slots then-modify-slots-failed-record
                  then-modify-slots-record then-parts then-print-to-user then-print-to-user failed-record
                  then-print-to-user-record to-delete to-delete-1 transpose unary-unit-op undefined
                  undefined-pred unit unit-op- unitized-alg unitized-defn worth los1 los2 los3 los4
                  los5 los6 los7 win1))


;; TODO - break these lexically out into topical groups
(defmacro defunit (&rest rest)
  `(putprops ,@rest))


(defunit int-applics
  worth 500
  isa (slot non-criterial-slot repr-concept anything)
  data-type unit
  double-check t
  dont-copy t
  super-slots (applics)
  less-interesting (applics))

(defunit mult-ele-struc-insert
  worth 500
  isa (math-concept math-op op anything struc-op mult-ele-struc-op binary-op)
  arity 2
  domain (anything mult-ele-struc)
  range (multi-ele-struc)
  elim-slots (applics)
  specializations (list-insert bag-insert)
  fast-alg cons)

(defunit rarity
  worth 500
  isa (slot non-criterial-slot repr-concept anything)
  data-type number
  dont-copy t
  format (frequency-true number-t number-f))

(defunit why-int
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  data-type next
  double-check t
  dont-copy t)

(defunit is-a-int
  worth 300
  inverse (int-examples)
  data-type unit
  double-check t
  isa (slot non-criterial-slot repr-concept anything))

(defunit int-examples
  worth 500
  isa (slot non-criterial-slot repr-concept anything)
  data-type unit
  double-check t
  dont-copy t
  super-slots (examples)
  inverse (is-a-int)
  less-interesting (examples))

(defunit less-interesting
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  data-type unit
  inverse (more-interesting))

(defunit more-interesting
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  data-type unit
  inverse (less-interesting))

(defunit interestingness
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  data-type lisp-pred
  double-check t
  abbrev ("What would make an instance of this unit interesting?")
  english ("What features or properties would an example or applic of this unit possess which would make it unusually interesting?"))

(defunit restrictions
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  data-type unit
  double-check t
  inverse (extensions)
  super-slots (specializations))

(defunit extensions
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  data-type unit
  double-check t
  inverse (restrictions)
  super-slots (generalizations))

(defunit op-cat-by-nargs
  worth 500
  isa (category anything repr-concept)
  examples (unary-pred binary-pred tertiary-pred unary-op binary-op tertiary-op)
  generalizations (category)
  specializations (pred-cat-by-nargs))

(defunit pred-cat-by-nargs
  worth 500
  isa (category anything repr-concept)
  examples (unary-pred binary-pred tertiary-pred)
  generalizations (category op-cat-by-nargs))

(defunit tertiary-pred
  lower-arity (binary-pred)
  worth 500
  generalizations (tertiary-op pred op anything)
  isa (repr-concept anything category pred-cat-by-nargs op-cat-by-nargs)
  fast-defn (lambda (f)
              (and (memb 'pred (isa f))
                   (eq 3 (arity f))))
  rarity (0.1827957 17 76))

(defunit unary-pred
  worth 500
  higher-arity (binary-pred)
  generalizations (unary-op pred op anything)
  isa (repr-concept anything category pred-cat-by-nargs op-cat-by-nargs)
  examples (always-t always-nil constant-unary-pred undefined-pred not)
  fast-defn (lambda (f)
              (and (memb 'pred (isa f))
                   (eq 1 (arity f))))
  rarity (0.1182796 11 82))

(defunit binary-pred
  worth 500
  lower-arity (unary-pred)
  higher-arity (tertiary-pred)
  generalizations (binary-op pred op anything)
  isa (repr-concept anything category pred-cat-by-nargs op-cat-by-nargs)
  examples (equal ieqp eq ileq igeq ilessp igreaterp and or the-second-of
                  the-first-of struc-equal set-equal subsetp constant-binary-pred
                  always-t-2 always-nil-2 o-set-equal bag-equal list-equal member memb
                  implies)
  fast-defn (lambda (f)
              (and (memb 'pred (isa f))
                   (eq 2 (arity f))))
  int-examples (ieqp eq struc-equal set-equal o-set-equal bag-equal list-equal memb member)
  rarity (0.07526882 7 86))

(defunit higher-arity
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  data-type unit
  inverse (lower-arity))

(defunit lower-arity
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  data-type unit
  inverse (higher-arity))

(defunit non-empty-struc
  worth 500
  isa (math-concept math-obj anything category type-of-structure)
  generalizations (structure anything set list bag mult-ele-struc o-set
                             no-mult-ele-struc ord-struc un-ord-struc pair o-pair)
  fast-defn #'consp
  examples nil)

(defunit empty-struc
  worth 500
  isa (math-concept math-obj anything category type-of-structure)
  generalizations (structure anything set list bag mult-ele-struc o-set
                             no-mult-ele-struc ord-struc un-ord-struc)
  fast-defn #'null
  elim-slots (examples))

(defunit set-of-sets
  isa (math-concept math-obj anything category)
  worth 500
  unitized-defn (lambda (s)
                  (and (run-defn 'set s)
                       (every (lambda (n) (run-defn 'set n)) s)))
  elim-slots (examples)
  generalizations (anything structure-of-structures)
  each-element-is-a set
  specializations (relation))

(defunit structure-of-structures
  isa (math-concept math-obj anything category)
  worth 500
  unitized-defn (lambda (s)
                  (and (run-defn 'structure s)
                       (every (lambda (n) (run-defn 'structure n)) s)))
  elim-slots (examples)
  generalizations (anything)
  each-element-is-a structure
  specializations (set-of-o-pairs set-of-sets))

(defunit truth-value
  generalizations (anything atom)
  worth 500
  isa (anything category math-obj)
  fast-defn (lambda (x)
              (or (eq x nil)
                  (eq x t)))
  examples (t nil))

(defunit atom
  generalizations (anything)
  worth 500
  isa (anything category repr-concept)
  fast-defn #'atom
  specializations (truth-value))

(defunit implies
  worth 500
  isa (op pred math-op math-pred anything binary-op logic-op binary-pred)
  arity 2
  domain (anything anything)
  range (anything)
  elim-slots (applics)
  fast-alg (lambda (x y)
             (or (null x) y))
  unitized-alg (lambda (x y)
                 (run-alg 'or (run-alg 'not x) y)))

(defunit not
  worth 500
  isa (op pred math-op math-pred anything unary-op logic-op unary-pred)
  arity 1
  domain (anything)
  range (bit)
  elim-slots (applics)
  fast-alg #'not)

(defunit logic-op
  generalizations (math-concept op math-op anything struc-op)
  worth 500
  isa (math-concept math-obj anything category)
  abbrev ("Logical operations")
  examples (and or the-first-of the-second-of not implies))

(defunit relation
  isa (math-concept math-obj anything category)
  worth 500
  unitized-defn (lambda (s)
                  (and (run-defn 'set s)
                       ;; BUGFIX - OPair missing a quote
                       (every (lambda (n) (run-defn 'o-pair n)) s))))

(defunit set-of-o-pairs
  isa (math-concept math-object anything category)
  worth 500
  unitized-defn (lambda (s)
                  (and (run-defn 'set s)
                       (every (lambda (n) (run-defn 'o-pair n)) s)))
  elim-slots (examples)
  generalizations (anything structure-of-structures)
  each-element-is-a o-pair
  specializations (relation))

(defunit invert-op
  worth 100
  isa (math-concept math-op op anything unary-op)
  arity 1
  domain (op)
  range (inverted-op)
  elim-slots (applics))

(defunit inverted-op
  generalizations (math-concept op math-op anything)
  worth 500
  isa (math-concept math-obj anything category)
  abbrev ("Operations which were formed via InvertOp")
  is-range-of (InvertOp))

(defunit restrict
  worth 600
  isa (math-concept math-op op anything unary-op)
  arity 1
  domain (op)
  range (op)
  elim-slots (applics)
  fast-alg (lambda (f)
             (let* ((garg (random-choose (subset (domain f) #'specializations)))
                    (newdom (random-subst (random-choose (specializations garg))
                                          garg
                                          (domain f))))
               (cond ((and garg ;; TODO - these 2 were setf'd here. Is there return value ever NIL?
                           newdom
                           (not (equal newdom (domain f))))
                      (let ((nam (create-unit (pack* 'restric f))))
                        (put nam 'isa (copy (isa f)))
                        (put nam 'worth (average-worths 'restrict f))
                        (put nam 'arity (arity f))
                        ;; Since MAPCAR exits when one list runs out, this gives var names per param in DOMAIN
                        (let ((fargs (mapcar #'the-second-of
                                             (domain f)
                                             '(u v w x y z z2 z3 z4 z5))))
                          (put nam 'domain newdom)
                          (put nam 'range (copy (range f)))
                          (put nam 'unitized-alg `(lambda ,fargs
                                                    (cons 'run-alg #',f ,@fargs))))
                        (put nam 'extensions (list f))
                        (put nam 'elim-slots '(applics))
                        (put nam 'creditors '(restrict))
                        (add-inv nam)
                        nam))
                     (t ;; ORIG: we should check for cases where 2 domain components of F have a common nontrivial specialization
                      'failed)))))

(defunit identity-1
  worth 500
  isa (math-concept math-op op anything unary-op)
  arity 1
  domain (anything)
  range (anything)
  elim-slots (applics)
  fast-alg (lambda (x) x)
  generalizations (proj1 proj2 proj-1-of-3 proj-2-of-3 proj-3-of-3))

(defunit proj-3-of-3
  worth 500
  isa (math-concept math-op anything tertiary-op)
  arity 3
  domain (anything anything anything)
  range (anything)
  elim-slots (applics)
  fast-alg (lambda (x y z)
             (declare (ignore x y))
             z)
  specializations (identity-1))

(defunit proj-2-of-3
  worth 500
  isa (math-concept math-op op anything tertiary-op)
  arity 3
  domain (anything anything anything)
  range (anything)
  elim-slots (applics)
  fast-alg (lambda (x y z)
             (declare (ignore x z))
             y)
  specializations (identity-1))

(defunit proj-1-of-3
  worth 500
  isa (math-concept math-op op anything tertiary-op)
  arity 3
  domain (anything anything anything)
  range (anything)
  elim-slots (applics)
  fast-alg (lambda (x y z)
             (declare (ignore y z))
             x)
  specializations (identity-1))

(defunit proj2
  worth 500
  isa (math-concept math-op op anything binary-op)
  arity 2
  domain (anything anything)
  range (anything)
  elim-slots (applic)
  fast-alg (lambda (x y)
             (declare (ignore x))
             y)
  specializations (identity-1))

(defunit proj1
  worth 500
  isa (math-concept math-op op anything binary-op)
  arity 2
  domain (anything anything)
  range (anything)
  elim-slots (applics)
  fast-alg (lambda (x y)
             (declare (ignore y))
             x)
  specializations (identity-1))

(defunit memb
  worth 500
  isa (math-concept math-op op math-pred pred anything binary-op binary-pred)
  fast-alg #'memb ;; original implementation: (lambda (x y) (memb x y))
  arity 2
  domain (anything structure)
  range (bit)
  elim-slots (applics)
  recursive-alg (lambda (x s)
                  (cond ((null s) nil)
                        ((eq x (car s)) t)
                        (t (run-alg 'memb x (cdr s)))))
  is-a-int (binary-pred)
  rarity (0.1.1 9))

(defunit member
  worth 500
  isa (math-concept math-op math-pred pred anything binary-op binary-pred)
  fast-alg #'member ;; original implementation: (lambda (x y) (member x y))
  arity 2
  domain (anything structure)
  range (bit)
  elim-slots (applics)
  recursive-alg (lambda (x s)
                  (cond ((null s) nil)
                        ((equal x (car s)) t)
                        (t (run-alg 'member x s))))
  is-a-int (binary-pred)
  rarity (0.1 1 9))

(defunit all-but-last
  worth 500
  isa (math-concept math-op op anything unary-op)
  arity 1
  domain (ord-struc)
  range (anything)
  elim-slots (applics)
  ;; OPTIMIZATION - not a very fast fast-alg, as this traverses twice.  just keep track of prior cell and NIL terminate it if we reach the last one.
  fast-alg (lambda (s)
             (ldiff s (last s))))

(defunit last-ele
  worth 500
  isa (math-concept math-op op anything unary-op)
  arity 1
  domain (ord-struc)
  range (anything)
  elim-slots (applics)
  fast-alg (lambda (s)
             (car (last s))))

(defunit all-but-third
  worth 500
  isa (math-concept math-op op anything unary-op)
  arity 1
  domain (ord-struc)
  range (anything)
  elim-slots (applics)
  fast-alg (lambda (s)
             (cons (car s)
                   (cons (cadr s)
                         (cdddr s)))))

(defunit all-but-second
  worth 500
  isa (math-concept math-op op anything unary-op)
  arity 1
  domain (ord-struc)
  range (anything)
  elim-slots (applics)
  fast-alg (lambda (s)
             (cons (car s)
                   (cddr s))))

(defunit all-but-first
  worth 500
  isa (math-concept math-op op anything unary-op)
  arity 1
  domain (ord-struc)
  range (anything)
  elim-slots (applics)
  fast-alg #'cdr)

(defunit third-ele
  worth 500
  isa (math-concept math-op op anything unary-op)
  arity 1
  domain (ord-struc)
  range (anything)
  elim-slots (applics)
  fast-alg #'caddr)

(defunit second-ele
  worth 500
  isa (math-concept math-op op anything unary-op)
  arity 1
  domain (ord-struc)
  range (anything)
  elim-slots (applics)
  fast-alg #'cadr
  rarity (0.85 17 3))

(defunit first-ele
  worth 500
  isa (math-concept math-op op anything unary-op)
  arity 1
  domain (ord-struc)
  range (anything)
  elim-slots (applics)
  fast-alg #'car)

(defunit reverse-o-pair
  worth 500
  isa (math-concept math-op op anything unary-op ord-struc-op list-op)
  arity 1
  domain (o-pair)
  range (o-pair)
  elim-slots (applics)
  fast-alg (lambda (p)
             (list (cadr p)
                   (car p))))

(defunit pair
  worth 500
  isa (math-concept math-obj anything category type-of-structure)
  ;; TODO - huh?
  generator ((nil)
             (get-a-o-pair)
             (old))
  fast-defn (lambda (s) (eq 2 (length s)))
  generalizations (anything structure mult-ele-struc un-ord-struc bag)
  specializations (non-empty-struc))

(defunit o-pair
  worth 500
  isa (math-concept math-obj anything category type-of-structure)
  generator ((nil)
             (get-a-o-pair)
             (old))
  fast-defn (lambda (s) (eq 2 (length s)))
  generalizations (anything structure mult-ele-struc ord-struc list)
  in-domain-of (reverse-o-pair)
  is-range-of (reverse-o-pair)
  specializations (non-empty-struc))

(defunit parallel-join-2
  worth 800
  isa (math-concept math-op op anything tertiary-op)
  arity 3
  domain (type-of-structure type-of-structure binary-op)
  range (binary-op)
  elim-slots (applics)
  fast-alg (lambda (s s2 f)
             ;; ORIG: note that S is the name of a type of structure, such as List, rather than a particular individual structure, such as (a b c d)
             (cond ((and (memb 'structure (generalizations s))
                         (memb 'structure (generalizations s2))
                         (memb 'op (isa f))
                         (eq 2 (length (domain f)))
                         (is-a-kind-of s2 (cadr (domain f)))
                         (or (eq 'anythign (car (domain f)))
                             (let ((typmem (each-element-is-a s)))
                               (and typmem
                                    (is-a-kind-of typmem (car (domain f)))))))
                    (let ((nam (create-unit (pack* 'join- f '-on- s 's '-with-a- 's2 '-as-param))))
                      (put nam 'isa (isa f))
                      (put nam 'worth (average-worths 'parallel-replace-2
                                                      (average-worths f (average-worths s s2))))
                      (put nam 'arity 2)
                      (put nam 'domain (list s s2))
                      (put nam 'range (list (let ((mu (pack* s '-of- (car (range f)) 's)))
                                              (if (unitp mu)
                                                  mu
                                                  (progn
                                                    (cprin1 21 "~% It might be nice to have a unit called "
                                                            mu "~%")
                                                    s)))))
                      (put nam 'unitized-alg (subst f 'f '(lambda (s s2)
                                                           (mapappend s (lambda (e)
                                                                          (run-alg 'f e s2))))))
                      (put nam 'elim-slots '(applics))
                      (put nam 'creditors 'parallel-replace-2)
                      (add-inv nam)
                      nam))
                   (t 'failed)))
  rarity (0.3272727 36 74))

(defunit parallel-join worth 800
  isa (math-concept math-op op anything binary-op)
  arity 2
  domain (type-of-structure unary-op)
  range (unary-op)
  elim-slots (applics)
  fast-alg (lambda (s f)
             ;; ORIG: note that S is the name of a type of structure, such as List, rather than a particular individual structure, such as (a b c d)
             (cond ((and (memb 'structure (generalization s))
                         (memb 'op (isa f))
                         (eq 1 (length (domain f)))
                         (or (eq 'anything (car (domain f)))
                             (let ((typmem (each-element-is-a s)))
                               (and typmem
                                    (is-a-kind-of typmem (car (domain f))))))
                         (is-a-kind-of (car (range f)) 'structure))
                    (let ((nam (create-unit (pack* 'join- f '-on- s 's))))
                      (put nam 'isa (copy (isa f)))
                      (put nam 'worth (average-worths 'parallel-join (average-worths f s)))
                      (put nam 'arity 1)
                      (put nam 'domain (list s))
                      (put nam 'range (list (let ((mu (pack* 'of (car (range f)) 's)))
                                              (cond ((unitp mu)
                                                     mu)
                                                    (t (cprin1 21 "~% It might be nice to have a unit called " mu "~%")
                                                       s)))))
                      (put nam 'unitized-alg (subst f 'f '(lambda (s)
                                                           (mapappend s (lambda (e)
                                                                          (run-alg 'f e))))))
                      (put nam 'elim-slots '(applics))
                      (put nam 'creditors '(parallel-join))
                      (add-inv nam)
                      nam))
                   (t ;; ORIG: we should check for cases where f could sub for other than the first arg of g
                    'failed))))

(defunit repeat2
  worth 800
  isa (math-concept math-op op anything tertiary-op)
  arity 3
  domain (type-of-structure type-of-structure tertiary-op)
  range (binary-op)
  elim-slots (applics)
  fast-alg (lambda (s s2 f)
             ;; ORIG: note that S is the name of a type of structure, such as List, rather than a particular individual structure, such as (a b c d)
             (cond ((and (memb 'structure (generalizations s))
                         (memb 'structure (generalizations s2))
                         (memb 'op (isa f))
                         (eq 3 (length (domain f)))
                         (or (eq 'anything (caddr (domain f)))
                             (let ((typmem (each-element-is-a s)))
                               (and typmem
                                    (is-a-kind-of typmem (caddr (domain f))))))
                         (is-a-kind-of (car (range f))
                                       (car (domain f)))
                         (is-a-kind-of s2 (cadr (domain f))))
                    (let ((nam (create-unit (pack* 'repeat2- f '-on- 's-with-a- s2 '-as-param))))
                      (put nam 'isa (cons 'binary-op (remove 'tertiary-op (isa f))))
                      (put nam 'worth (average-worths 'repeat2 (average-worths f (average-worths s s2))))
                      (put nam 'arity 2)
                      (put nam 'domain (list s s2))
                      (put nam 'range (copy (range f)))
                      (put nam 'unitized-alg (subst f 'f '(lambda (s s2 v)
                                                           (setf v (car s))
                                                           (mapc (lambda (e)
                                                                   (setf v (run-alg 'f v s2 e)))
                                                            (cdr s))
                                                           v)))
                      (put nam 'elim-slots '(applics))
                      (put nam 'creditors '(repeat2))
                      (add-inv nam)
                      nam))
                   (t ;; ORIG:  we should check for cases where f could sub for other than the first arg of g
                    'failed)))
  rarity (0.2295082 14 47))

(defunit tertiary-op
  generalizations (op anything)
  worth 500
  isa (repr-concept anything category op-cat-by-nargs)
  examples (parallel-replace-2 repeate2 parallel-join-2 proj-1-of-3 proj-2-of-3 proj-3-of-3)
  in-domain-of (repeat2)
  lower-arity (binary-op)
  specializations (tertiary-pred)
  fast-defn (lambda (f)
              (eq 3 (arity f)))
  rarity (0.3978495 37 56))

(defunit repeat
  worth 800
  isa (math-concept math-op op anything binary-op)
  arity 2
  domain (type-of-structure binary-op)
  range (unary-op)
  elim-slots (applics)
  fast-alg (lambda (s f)
             ;; ORIG: note that S is the name of a type of structure, such as List, rather than a particular individual structure, such as (a b c d)
             (cond ((and (memb 'structure (generalizations s))
                         (memb 'op (isa f))
                         (eq 2 (length (domain f)))
                         (or (eq 'anything (cadr (domain f)))
                             (let ((typmem (each-element-is-a s)))
                               (and typmem
                                    (is-a-kind-of typmem (cadr (domain f))))))
                         (is-a-kind-of (car (range f))
                                       (car (domain f))))
                    (let ((nam (create-unit (pack* 'repeat- f '-on- s 's))))
                      (put nam 'isa (subst 'unary-op 'binary-op (isa f)))
                      (put nam 'worth (average-worths 'repeat (average-worths f s)))
                      (put nam 'arity 1)
                      (put nam 'domain (list s))
                      (put nam 'range (copy (range f)))
                      (put nam 'unitized-alg
                           (subst f 'f '(lambda (s v)
                                         ;; TODO - idiomize this loop, is this a REDUCE?
                                         (setf v (car s))
                                         (mapc (lambda (e)
                                                 (setf v (run-alg 'f v e)))
                                          (cdr s))
                                         v)))
                      (put nam 'elim-slots '(applics))
                      (put nam 'creditors 'repeat)
                      (add-inv nam)
                      nam))
                   (t ;; ORIG: we should check for cases where f could sub for other than the first arg of g
                    'failed)))
  rarity (0.3555556 16 29))

(defunit binary-op
  in-domain-of (parallel-replace-2 repeat parallel-join-2)
  generalizations (op anything)
  worth 500
  examples (parallel-replace bag-difference o-set-difference list-difference
                             set-difference struc-difference bag-union list-union
                             o-set-union struc-union bag-intersect set-union set-intersect
                             ord-struc-equal bag-equal list-equal o-set-equal o-set-delete
                             o-set-insert mult-ele-struc-delete-1 bag-delete-1 bag-delete
                             bag-insert list-delete-1 list-delete list-insert set-delete
                             set-insert struc-delete struc-insert and add always-nil-2
                             always-t-2 compose eq equal ieqp igeq igreaterp ileq
                             ilessp multiply or set-equal struc-equal subsetp
                             the-first-of the-second-of repeat parallel-join member memb
                             proj1 proj2 implies mult-ele-struc-insert)
  isa (repr-concept anything category op-cat-by-nargs)
  is-range-of (parallel-replace-2 repeat2 parallel-join-2)
  lower-arity (unary-op)
  higher-arity (tertiary-op)
  specializations (binary-pred)
  fast-defn (lambda (f)
              (eq 2 (arity f)))
  rarity (0.1827957 17 76))

(defunit parallel-replace-2
  worth 800
  isa (math-concept math-op op anything tertiary-op)
  arity 3
  domain (type-of-structure type-of-structure binary-op)
  range (binary-op)
  elim-slots (applics)
  fast-alg (lambda (s s2 f)
             ;; ORIG: note that S is the name of a type of structure, such as List, rather than a particular individual structure, such as (a b c d)
             (cond ((and (memb 'structure (generalizations s))
                         (memb 'structure (generalizations s2))
                         (memb 'op (isa f))
                         (eq 2 (length (domain f)))
                         (is-a-kind-of s2 (cadr (domain f)))
                         (or (eq 'anything (car (domain f)))
                             (let ((typmem (each-element-is-a s)))
                               (and typmem
                                    (is-a-kind-of typmem (car (domain f)))))))
                    (let ((nam (create-unit (pack* 'perform- f '-on- s 's-with-a- s2 '-as-param))))
                      (put nam 'isa (isa f))
                      (put nam 'worth (average-worths 'parallel-replace-2 (average-worths f (average-worths s s2))))
                      (put nam 'arity 2)
                      (put nam 'domain (list s s2))
                      (put nam 'range (list
                                       (let ((mu (pack* s '-of- (car (range f)) 's)))
                                         (cond ((unitp mu)
                                                mu)
                                               (t (cprin1 21 "~% It might be nice to have a unit called " mu "~%")
                                                  s)))))
                      (put nam 'unitized-alg (subst f 'f '(lambda (s s2)
                                                           (mapcar (lambda (e)
                                                                     (run-alg 'f e s2))
                                                            s))))
                      (put nam 'elim-slots '(applics))
                      (put nam 'creditors '(parallel-replace-2))
                      (add-inv nam)
                      nam))
                   (t 'failed)))
  rarity (0.375 3 5))

(defunit each-element-is-a
  worth 600
  isa (slot criterial-slot repr-concept anything)
  data-type unit)

(defunit unary-op
  generalizations (op anything)
  worth 500
  examples (coalesce always-nil always-t best-choose best-subset constant-binary-pred
                     constant-unary-pred divisors-of good-choose good-subset
                     random-choose random-subset square successor undefined-pred
                     reverse-o-pair first-ele second-ele third-ele all-but-first
                     all-but-second all-but-third last-ele all-but-last identity1 restrict
                     invert-op not)
  isa (repr-concept anything category op-cat-by-nargs)
  in-domain-of (parallel-replace parallel-join)
  is-range-of (parallel-replace repeat parallel-join)
  higher-arity (binary-op)
  specializations (unary-pred)
  fast-defn (lambda (f)
              (eq 1 (arity f)))
  rarity (0.2473118 23 70))

(defunit type-of-structure
  in-domain-of (parallel-replace parallel-replace-2 repeat repeat2 parallel-join
                                 parallel-join-2)
  worth 500
  isa (category anything repr-concept)
  examples (set list bag mult-ele-struc o-set no-mult-ele-struc ord-struc
                un-ord-struc o-pair pair empty-struc non-empty-struc)
  generalizations (category))

(defunit parallel-replace
  worth 888
  isa (math-concept math-op op anything binary-op)
  arity 2
  domain (type-of-structure unary-op)
  range (unary-op)
  elim-slots (applics)
  fast-alg (lambda (s f)
             ;; ORIG: note that S is the name of a type of structure, such as List, rather than a particular individual structure, such as (a b c d)
             (cond ((and (memb 'structure (generalizations s))
                         (memb 'op (isa f))
                         (eq 1 (length (domain f)))
                         (or (eq 'anything (car (domain f)))
                             (let ((typmem (each-element-is-a s)))
                               (and typmem
                                    (is-a-kind-of typmem (car (domain f)))))))
                    (let ((nam (create-unit (pack* 'perform- f '-on- s 's))))
                      (put nam 'isa (copy (isa f)))
                      (put nam 'worth (average-worths 'parallel-replace (average-worths f s)))
                      (put nam 'arity 1)
                      (put nam 'domain (list s))
                      ;; TODO - abstract out this existence check?
                      (put nam 'range (list (let ((mu (pack* s '-of- (car (range f)) '-s)))
                                              (cond ((unitp mu)
                                                     mu)
                                                    (t (cprin1 21 "~% It might be nice to have a unit called " mu "~%")
                                                       s)))))
                      (put nam 'unitized-alg (subst f 'f '(lambda (s)
                                                           (mapcar (lambda (e)
                                                                     (run-alg 'f e))
                                                            s))))
                      (put nam 'elim-slots '(applics))
                      (put nam 'creditors '(parallel-replace))
                      (add-inv nam)
                      nam))
                   (t ;; ORIG: we should check for cases where f could sub for other than the first arg of g
                    'failed)))
  rarity (0.2372881 14 45))

(defunit coalesce
  worth 900
  isa (math-concept math-op op anything unary-op)
  arity 1
  domain (op)
  range (op)
  elim-slots (applics)
  fast-alg (lambda (f)
             (let ((coargs (random-pair (domain f) 'is-a-kind-of)))
               (cond (coargs
                      (let ((nam (create-unit (pack* 'coa- f))))
                        (put nam 'isa (set-diff (isa f) (examples 'op-cat-by-nargs)))
                        ;; ORIG: We really should check that each such unit still claims Coa-f as an example -- eg, suppose f was a BinaryPred
                        (put nam 'worth (average-worths 'coalesce f))
                        (put nam 'arity (1- (arity f)))
                        (let* ((fargs (mapcar #'the-second-of
                                              (domain f)
                                              '(u v w x y z z2 z3 z4 z5)))
                               (newargs (copy fargs)))
                          ;; TODO - unravel this operation
                          (rplaca (nth newargs (cadr coargs))
                                  (car (nth newargs (car coargs))))
                          ;; TODO - can this be hoisted up to the prior LET? does the RPLACA above mutate this?
                          (let ((newdom (copy (domain f))))
                            (rplaca (nth newdom (cadr coargs))
                                    (car (nth newdom (car coargs))))
                            (if (<= (cadr coargs) 1)
                                (pop newdom)
                                (rplacd (nth newdom (1- (cadr coargs)))
                                        (cdr (nth newdom (cadr coargs)))))
                            (if (<= (cadr coargs) 1)
                                (pop fargs)
                                (rplacd (nth fargs (1- (cadr coargs)))
                                        (cdr (nth fargs (cadr coargs)))))
                            (put nam 'domain newdom)
                            (put nam 'range (copy (range f)))
                            (put nam 'unitized-alg `(lambda ,fargs
                                                      (run-alg ',f ,@newargs)))
                            (put nam 'elim-slots '(applics))
                            (put nam 'creditors '(coalesce))
                            (put nam 'isa (append (isa nam)
                                                  (subset (examples 'op-cat-by-nargs)
                                                          (lambda (pc)
                                                            (run-defn pc nam)))))
                            (add-inv nam)
                            nam))))
                     (t ;; ORIG: we should check for cases where 2 domain components of f have a common nontrivial specialization
                      'failed))))
  rarity (0.3928571 22 34))

(defunit bag-difference
  worth 500
  isa (math-concept math-op op anything struc-op bag-op binary-op)
  arity 2
  domain (bag bag)
  range (bag)
  elim-slots (applics)
  recursive-alg (lambda (s1 s2)
                  (cond ((null s1) nil)
                        ((member (car s2) s2)
                         (run-alg 'bag-delete-1 (car s1) s2))
                        (t (cons (car s1)
                                 (run-alg 'bag-difference
                                          (cdr s1)
                                          (run-alg 'bag-delete-1
                                                   (car s2)
                                                   s2))))))
  generalizations (struc-difference))

(defunit o-set-difference
  worth 500
  isa (math-concept math-op op anything struc-op o-set-op binary-op)
  arity 2
  domain (o-set o-set)
  range (o-set)
  elim-slots (applics)
  fast-alg #'set-difference
  recursive-alg (lambda (s1 s2)
                  (cond ((null s1) nil)
                        ((member (car s1) s2)
                         (run-alg 'o-set-difference (cdr s1) s2))
                        (t (cons (car s1)
                                 (run-alg 'o-set-difference (cdr s1) s2)))))
  generalizations (struc-difference))

(defunit list-difference worth 500
  isa (math-concept math-op op anything struc-op list-op binary-op)
  arity 2
  domain (list list)
  range (list)
  elim-slots (applics)
  recursive-alg (lambda (s1 s2)
                  (cond ((null s1) nil)
                        ((member (car s1) s2)
                         (run-alg 'list-difference
                                  (cdr s1)
                                  (run-alg 'list-delete-1 (car s1) s2)))
                        (t (cons (car s2)
                                 (run-alg 'list-difference
                                          (cdr s1)
                                          (run-alg 'list-delete-1 (car s1) s2))))))
  generalizations (struc-difference))

(defunit set-difference
  worth 500
  isa (math-concept math-op op anything struc-op set-op binary-op)
  arity 2
  domain (set set)
  range (set)
  elim-slots (applics)
  fast-alg #'set-difference
  recursive-alg (lambda (s1 s2)
                  (cond ((null s1) nil)
                        ((member (car s1) s2)
                         (run-alg 'set-difference (cdr s1) s2))
                        (t (cons (car s1)
                                 (run-alg 'set-difference (cdr s1) s2)))))
  generalizations (struc-difference))

(defunit struc-difference
  worth 500
  isa (math-concept math-op op anything struc-op binary-op)
  arity 2
  domain (structure structure)
  range (structure)
  elim-slots (applics)
  specializations (set-difference list-difference o-set-difference
                                  bag-difference))

(defunit bag-union
  worth 500
  isa (math-concept math-op op anything struc-op binary-op)
  arity 2
  domain (bag bag)
  range (bag)
  elim-slots (applics)
  recursive-alg (lambda (s1 s2)
                  (cond ((null s1) s2)
                        (t (run-alg 'bag-insert (car s1)
                                    (run-alg 'bag-union (cdr s1)
                                             (run-alg 'bag-delete-1 (car s1) s2))))))
  generalizations (struc-union))

(defunit list-union
  worth 500
  isa (math-concept math-op op anything struc-op list-op binary-op)
  arity 2
  domain (list list)
  range (list)
  elim-slots (applics)
  fast-alg #'append
  recursive-alg (lambda (s1 s2)
                  (cond ((null s1) s2)
                        (t (cons (car s1)
                                 (run-alg 'list-union (cdr s1) s2)))))
  generalizations (struc-union))

(defunit o-set-union
  worth 500
  isa (math-concept math-op op anything struc-op o-set-op binary-op)
  arity 2
  domain (o-set o-set)
  range (o-set)
  elim-slots (applics)
  fast-alg #'set-union
  recursive-alg (lambda (s1 s2)
                  (cond ((null s1) s2)
                        ((member (car s1) s2)
                         (run-alg 'o-set-union (cdr s1) s2))
                        (t (cons (car s1)
                                 (run-alg 'o-set-union (cdr s1) s2)))))
  generalizations (struc-union))

(defunit struc-union
  worth 500
  isa (math-concept math-op op anything struc-op binary-op)
  arity 2
  domain (structure structure)
  range (structure)
  elim-slots (applics)
  specializations (set-union o-set-union list-union bag-union))

(defunit bag-intersect
  worth 500
  isa (math-concept math-op op anything struc-op bag-op binary-op)
  arity 2
  domain (bag bag)
  range (bag)
  elim-slots (applics)
  iterative-alg (lambda (s1 s2)
                  (dolist (x (copy-list s1))
                    (cond ((member x s2)
                           (setf s2 (run-alg 'bag-delete-1 x s2)))
                          (t (setf s1 (run-alg 'bag-delete-1 x s1)))))
                  s1)
  generalizations (struc-intersect))

(defunit o-set-intersect
  worth 500
  isa (math-concept math-op op anything struc-op o-set-op binary-op)
  arity 2
  domain (o-set o-set)
  range (o-set)
  elim-slots (applics)
  fast-alg #'o-set-intersect
  recursive-alg (lambda (s1 s2)
                  (cond ((null s1) nil)
                        ((member (car s1) s2)
                         (cons (car s1)
                               (run-alg 'o-set-intersect (cdr s1) s2)))
                        (t (run-alg 'o-set-intersect (cdr s1) s2))))
  generalizations (struc-intersect))

(defunit list-intersect
  worth 500
  isa (math-concept math-op op anything struc-op list-op binary-op)
  arity 2
  domain (list list)
  range (list)
  elim-slots (applics)
  recursive-alg (lambda (s1 s2)
                  (cond ((null s1) nil)
                        ((member (car s1) s2)
                         (cons (car s1)
                               (run-alg 'list-intersect (cdr s1)
                                        (run-alg 'list-delete-1 (car s1) s2))))
                        (t (run-alg 'list-intersect (cdr s1) s2))))
  generalizations (struc-intersect))

(defunit struc-intersect
  worth 500
  isa (math-concept math-op op anything struc-op binary-op)
  arity 2
  domain (structure structure)
  range (structure)
  elim-slots (applics)
  specializations (set-intersect list-intersect o-set-intersect bag-intersect))

(defunit set-union
  worth 500
  isa (math-concept math-op op anyting struc-op set-op binary-op)
  arity 2
  domain (set set)
  range (set)
  elim-slots (applics)
  fast-alg #'set-union
  recursive-alg (lambda (s1 s2)
                  (cond ((null s1) s2)
                        ((member (car s1) s2)
                         (run-alg 'set-union (cdr s1) s2))
                        (t (cons (car s1)
                                 (run-alg 'set-union (cdr s1) s2)))))
  generalizations (struc-union))

(defunit set-intersect
  worth 500
  isa (math-concept math-op anything struc-op set-op binary-op)
  arity 2
  domain (set set)
  range (set)
  elim-slots (applics)
  fast-alg #'set-intersect
  recursive-alg (lambda (s1 s2)
                  (cond ((null s1) nil)
                        ((member (car s1) s2)
                         (cons (car s1)
                               (run-alg 'set-intersect (cdr s1) s2)))
                        (t (run-alg 'set-intersect (cdr s1) s2))))
  generalizations (struc-intersect))

(defunit ord-struc-op
  generalizations (math-concept op math-op anything struc-op)
  worth 500
  isa (math-concept math-obj anything category)
  abbrev ("Operations on structures which are ordered")
  specializations (list-op o-set-op)
  examples (ord-struc-equal reverse-o-pair))

(defunit ord-struc-equal
  worth 500
  isa (math-concept math-op anything struc-op ord-struc-op binary-op)
  arity 2
  domain (ord-struc ord-struc)
  range (anything)
  elim-slots (applics)
  specializations (list-equal o-set-equal)
  fast-alg #'equal)

(defunit bag-equal
  worth 500
  isa (math-concept math-op op math-pred pred anything struc-op bag-op binary-op binary-pred)
  arity 2
  domain (bag bag)
  range (bit)
  elim-slots (applics)
  generalizations (equal struc-equal)
  recursive-alg (lambda (s1 s2)
                  (cond ((and (null s1)
                              (null s2))
                         t)
                        (t (and (consp s1)
                                (consp s2)
                                (member (car s1) s2)
                                (run-alg 'bag-equal (cdr s2) (run-alg 'bag-delete-1 (car s1) s2))))))
  specializations (list-equal)
  is-a-int (binary-pred)
  rarity (0.1 1 9))

(defunit list-equal
  worth 500
  isa (math-concept math-op op math-pred pred anything struc-op list-op binary-op binary-pred)
  arity 2
  domain (list list)
  range (bit)
  elim-slots (applics)
  generalizations (equal struc-equal bag-equal ord-struc-equal)
  recursive-alg (lambda (s1 s2)
                  (cond ((and (null s1)
                              (null s2))
                         t)
                        (t (and (consp s1)
                                (consp s2)
                                (equal (car s1) (car s2))
                                (run-alg 'list-equal (cdr s1) (cdr s2))))))
  fast-alg #'equal
  is-a-int (binary-pred)
  rarity (0.1 1 9))

(defunit o-set-equal
  worth 500
  isa (math-concept math-op op math-pred pred anything struc-op o-set-op binary-op binary-pred)
  arity 2
  domain (o-set o-set)
  range (bit)
  elim-slots (applics)
  generalizations (equal struc-equal subsetp set-equal ord-struc-equal)
  recursive-alg (lambda (s1 s2)
                  (cond ((and (null s1) (null s2))
                         t)
                        (t (and (consp s1)
                                (consp s2)
                                (equal (car s1) (car s2))
                                (run-alg 'o-set-equal (cdr s1) (cdr s2))))))
  fast-alg #'equal
  is-a-int (binary-pred)
  rarity (0.1 1 9))

(defunit suf-defn
  worth 600
  isa (slot criterial-slot repr-concept anything)
  data-type lisp-pred
  generalizations (defn)
  super-slots (defn))

(defunit nec-defn
  worth 600
  isa (slot criterial-slot repr-concept anything)
  data-type lisp-pred
  generalizations (defn)
  super-slots (defn))

(defunit un-ord-struc
  worth 500
  isa (math-concept math-obj anything category type-of-structure)
  specializations (bag set pair empty-struc non-empty-struc)
  generalizations (structure anything))

(defunit ord-struc
  worth 500
  isa (math-concept math-obj anything category type-of-structure)
  specializations (list o-set o-pair empty-struc non-empty-struc)
  generalizations (structure anything)
  in-domain-of (ord-struc-equal all-but-first firsrt-ele second-ele third-ele all-but-second
                                all-but-third last-ele all-but-last))

(defunit no-mult-ele-struc
  worth 500
  isa (math-concept math-obj anything category type-of-structure)
  specializations (set o-set empty-struc non-empty-struc)
  generalizations (structure anything)
  nec-defn #'no-repeats-in)

(defunit o-set-delete
  worth 500
  isa (math-concept math-op op anything struc-op o-set-op binary-op)
  arity 2
  domain (anything o-set)
  range (o-set)
  elim-slots (applics)
  recursive-alg (lambda (x s)
                  (cond ((null s) nil)
                        ((equal x (car s))
                         (cdr s))
                        (t (cons (car s)
                                 (run-alg 'o-set-delete x (cdr s))))))
  fast-alg #'remove
  generalizations (struc-delete))

(defunit o-set-op
  generalizations (math-concept op math-op anything struc-op ord-struc-op)
  worth 500
  isa (math-concept math-obj anything category)
  abbrev ("O-Set Operations")
  examples (o-set-insert o-set-delete o-set-equal o-set-intersect o-set-union o-set-difference))

(defunit o-set-insert
  worth 500
  isa (math-concept math-op op anything struc-op o-set-op binary-op)
  arity 2
  domain (anything o-set)
  range (o-set)
  elim-slots (applics)
  recursive-alg (lambda (x s)
                  (cond ((null s)
                         (cons x s))
                        ((equal x (car s))
                         s)
                        (t (cons (car s)
                                 (run-alg 'o-set-insert x (cdr s))))))
  generalizations (struc-insert)
  fast-alg (lambda (x s)
             (cond ((member x s)
                    s)
                   (t (cons (car s)
                            (run-alg 'o-set-insert x (cdr s)))))))

(defunit o-set
  worth 500
  isa (math-concept math-obj anything category type-of-structure)
  generator ((nul)
             (get-a-set)
             (old))
  fast-defn (lambda (s)
              (or (eq s nil)
                  (no-repeats-in s)))
  recursive-defn (lambda (s)
                   (if (consp s)
                       (and (not (member (car s) (cdr s)))
                            (run-defn 'o-set (cdr s)))
                       (eq s nil)))
  generalizations (anything structure bag list set no-mult-ele-struc ord-struc)
  in-domain-of (o-set-insert o-set-delete o-set-equal o-set-intersect o-set-union o-set-difference)
  is-range-of (o-set-insert o-set-delete o-set-intersect o-set-union o-set-difference)
  specializations (empty-struc non-empty struc)
  rarity (0 2 2)
  elim-slots (examples))

(defunit mult-ele-struc-delete-1
  worth 500
  isa (math-concept math-op op anything struc-op mult-ele-struc-op binary-op)
  arity 2
  domain (anything mult-ele-struc)
  range (mult-ele-struc)
  elim-slots (applics)
  specializations (list-delete-1 bag-delete-1)
  recursive-alg (lambda (x s)
                  (cond ((null s) nil)
                        ((equal x (car s))
                         (cdr s))
                        (t (cons (car s)
                                 (run-alg 'mult-ele-struc-delete-1 x (cdr s)))))))

(defunit mult-ele-struc-op
  generalizations (math-concept op math-op anything struc-op)
  worth 500
  isa (math-concept math-obj anything category)
  abbrev ("Operations on structures which have multiple elements")
  specializations (list-op bag-op)
  examples (mult-ele-struc-delete-1 mult-ele-struc-insert))

(defunit mult-ele-struc
  worth 500
  isa (math-concept math-obj anything category type-of-structure)
  specializations (list bag o-pair pair empty-struc non-empty-struc)
  generalizations (structure anything)
  in-domain-of (mult-ele-struc-delete-1 mult-ele-struc-insert)
  is-range-of (mult-ele-struc-delete-1 mult-ele-struc-insert)
  suf-defn #'repeats-in)

(defunit bag-delete-1
  worth 500
  isa (math-concept math-op op anything struc-op bag-op binary-op)
  arity 2
  domain (anything bag)
  range (bag)
  elim-slots (applics)
  recursive-alg (lambda (x s)
                  (cond ((null s) nil)
                        ((equal x (car s))
                         (cdr s))
                        (t (cons (car s)
                                 (run-alg 'bag-delete-1 x (cdr s))))))
  generalizations (mult-ele-struc-delete-1))

(defunit bag-delete
  worth 500
  isa (math-concept math-op op anything struc-op bag-op binary-op)
  arity 2
  domain (anything bag)
  range (bag)
  elim-slots (applics)
  recursive-alg (lambda (x s)
                  (cond ((null s) nil)
                        ((equal x (car s))
                         (run-alg 'bag-delete x (cdr s)))
                        (t (cons (car s)
                                 (run-alg 'bag-delete x (cdr s))))))
  fast-alg #'remove
  generalizations (struc-delete))

(defunit bag-op
  generalizations (math-concept op math-op anything struc-op mult-ele-struc-op)
  worth 500
  isa (math-concept math-obj anything category)
  abbrev ("Bag Operations")
  examples (bag-insert bag-delete bag-delete-1 bag-equal bag-intersect bag-union bag-difference))

(defunit bag-insert
  worth 500
  isa (math-concept math-op op anything struc-op bag-op binary-op)
  arity 2
  domain (anything bag)
  range (bag)
  elim-slots (applics)
  fast-alg #'cons
  generalizations (struc-insert mult-ele-struc-insert))

(defunit bag
  worth 500
  isa (math-concept math-obj anything category type-of-structure)
  generator ((nil)
             (get-a-list)
             (old))
  fast-defn #'listp
  recursive-defn (lambda (s)
                   (cond ((not (consp s))
                          (eq s nil))
                         (t (run-defn 'bag (cdr s)))))
  generalizations (anything structure mult-ele-struc un-ord-struc)
  specializations (set o-set pair empty-struc non-empty-struc)
  in-domain-of (bag-insert bag-delete bag-delete-1 bag-equal bag-intersect bag-union bag-difference)
  is-range-of (bag-insert bag-delete bag-delete-1 bag-intersect bag-union bag-difference)
  rarity (0 2 2)
  elim-slots (examples))

(defunit list-delete-1
  worth 500
  isa (math-concept math-op anything struc-op list-op binary-op)
  arity 2
  domain (anything list)
  range (list)
  elim-slots (applics)
  recursive-alg (lambda (x s)
                  (cond ((null s) nil)
                        ((equal x (car s))
                         (cdr s))
                        (t (cons (car s)
                                 (run-alg 'list-delete-1 x (cdr s))))))
  generalizations (mult-ele-struc-delete-1))

(defunit list-delete
  worth 500
  isa (math-concept math-op op anything struc-op list-op binary-op)
  arity 2
  domain (anything list)
  range (list)
  elim-slots (applics)
  fast-alg #'remove
  recursive-alg (lambda (x s)
                  (cond ((null s) nil)
                        ((equal x (car s))
                         (run-alg 'list-delete x (cdr s)))
                        (t (cons (car s)
                                 (run-alg 'list-delete x (cdr s))))))
  generalizations (struc-delete))

(defunit list
  worth 500
  isa (math-concept math-obj anything category type-of-structure)
  generator ((nil)
             (get-a-list)
             (old))
  fast-defn #'listp
  recursive-defn (lambda (s)
                   (cond ((not (consp s))
                          ;; Checking for proper list termination
                          (eq s nil))
                         (t (run-defn 'list (cdr s)))))
  generalizations (anything structure mult-ele-struc ord-struc)
  is-range-of (list-insert list-delete list-delete-1 list-intersect list-union list-difference)
  in-domain-of (list-insert list-delete list-delete-1 list-equal list-intersect list-union list-difference)
  specializations (set o-set o-pair empty-struc non-empty-struc)
  rarity (0 2 2)
  elim-slots (examples))

(defunit list-insert
  worth 500
  isa (math-concept math-op op anything struc-op list-op binary-op)
  arity 2
  domain (anything list)
  range (list)
  elim-slots (applics)
  fast-alg #'cons
  generalizations (struc-insert mult-ele-struc-insert))

(defunit list-op
  generalizations (math-concept op math-op anything struc-op mult-ele-struc-op ord-struc-op)
  worth 500
  isa (math-concept math-obj anything category)
  abbrev ("List Operations")
  examples (list-insert list-delete list-delete-1 list-equal list-intersect list-union
                        list-difference reverse-o-pair))

(defunit set-delete
  worth 500
  isa (math-concept math-op op anything struc-op set-op binary-op)
  arity 2
  domain (anything set)
  range (set)
  elim-slots (applics)
  recursive-alg (lambda (x s)
                  (cond ((null s) nil)
                        ((equal x (car s))
                         (cdr s))
                        (t (cons (car s)
                                 (run-alg 'set-delete x (cdr s))))))
  fast-alg #'remove
  generalizations (struc-delete))

(defunit set-insert
  worth 500
  isa (math-concept math-op op anything struc-op set-op binary-op)
  arity 2
  domain (anything set)
  range (set)
  elim-slots (applics)
  fast-alg (lambda (x s)
             (cond ((member x s) s)
                   (t (cons x s))))
  recursive-alg (lambda (x s)
                  (cond ((null s)
                         (cons x s))
                        ((equal x (car s))
                         s)
                        (t (cons (car s)
                                 (run-alg 'set-insert x (cdr s))))))
  generalizations (struc-insert))

(defunit struc-delete
  worth 500
  isa (math-concept math-op op anything struc-op binary-op)
  arity 2
  domain (anything structure)
  range (structure)
  elim-slots (applics)
  specializations (list-delete bag-delete set-delete o-set-delete))

(defunit struc-op
  generalizations (math-concept op math-op anything)
  worth 500
  isa (math-concept math-obj anything category)
  abbrev ("Operations on structures")
  examples (struc-insert struc-delete random-choose random-subset good-choose best-choose
                         best-subset good-subset set-insert set-delete list-insert
                         list-delete list-delete-1 bag-insert bag-delete bag-delete-1
                         mult-ele-struc-delete-1 o-set-insert o-set-delete o-set-equal
                         set-equal bag-equal list-equal ord-struc-equal set-intersect
                         set-union struc-intersect list-intersect o-set-intersect
                         bag-intersect struc-union o-set-union list-union bag-union
                         struc-difference set-difference list-difference o-set-difference
                         bag-difference mult-ele-struc-insert)
  specializations (set-op list-op bag-op mult-ele-struc-op o-set-op ord-struc-op logic-op))

(defunit struc-insert
  worth 500
  isa (math-concept math-op op anything struc-op binary-op)
  arity 2
  domain (anything structure)
  range (structure)
  elim-slots (applics)
  specializations (list-insert bag-insert set-insert o-set-insert))

(defunit and
  worth 569
  isa (op pred math-op math-pred anything binary-op logic-op binary-pred)
  fast-alg (lambda (x y)
             (and x y))
  arity 2
  domain (anything anything)
  range (anything)
  elim-slots (applics)
  generalizations (the-second-of the-first-of or)
  rarity (1.0 2 0))

(defunit abbrev
  worth 307
  isa (slot non-criterial-slot repr-concept anything)
  data-type text)

(defunit add
  worth 500
  isa (math-concept math-op op num-op anything binary-op)
  fast-alg (lambda (x y)
             (+ x y))
  recursive-alg (lambda (x y)
                  (cond ((eq x 0)
                         y)
                        (t (run-alg 'successor (run-alg 'add (1- x) y)))))
  unitized-alg (lambda (x y)
                 (cond ((eq x 0) y)
                       (t (run-alg 'successor (run-alg 'add (1- x) y)))))
  iterative-alg (lambda (x y)
                  (loop for i from 1 to x
                        do (incf y))
                  y)
  arity 2
  domain (nnumber nnumber)
  range (nnumber)
  elim-slots (applics))

(defunit alg
  worth 600
  isa (slot criterial-slot repr-concept anything)
  data-type lisp-fn
  sub-slots (fast-alg iterative-alg recursive-alg unitized-alg))

(defunit always-nil
  worth 500
  isa (op pred anything constant-pred unary-op math-op unary-pred)
  arity 1
  domain (anything)
  range (bit)
  elim-slots (applics)
  generalizations (constant-unary-pred)
  fast-alg (lambda (x)
             (declare (ignore x))
             nil))

(defunit always-nil-2
  worth 500
  isa (op pred anything constant-pred binary-op math-op binary-pred)
  arity 2
  domain (anything anything)
  range (bit)
  elim-slots (applics)
  generalizations (constant-binary-pred)
  fast-alg (lambda (x y)
             (declare (ignore x y))
             nil))

(defunit always-t
  worth 500
  isa (op pred anything constant-pred unary-op math-op unarypred)
  arity 1
  domain (anything)
  range (bit)
  elim-slots (applics)
  generalizations (constant-unary-pred)
  fast-alg (lambda (x)
             (declare (ignore x))
             t))

(defunit always-t-2
  worth 500
  isa (op pred anything constant-pred binary-op math-op binary-pred)
  arity 2
  domain (anything anything)
  range (bit)
  elim-slots (applics)
  generalizations (constant-binary-pred)
  fast-alg (lambda (x y)
             (declare (ignore x y))
             t))

(defunit anything
  worth 550
  specializations (set heuristic slot nnumber unit prime-num conjecture even-num
                       task odd-num perf-num perf-square set-of-numbers criterial-slot
                       bit non-criterial-slot hind-sight-rule unary-unit-op math-concept
                       repr-concept math-op math-obj set-op unit-op num-op math-pred op
                       pred record-slot structure constant-pred struc-op list-op list
                       bag bag-op mult-ele-struc-op mult-ele-struc o-set o-set-op
                       no-mult-ele-struc ord-struc un-ord-struc ord-struc-op unary-op
                       binary-op tertiary-op o-pair pair inverted-op set-of-o-pairs
                       relation logic-op atom truth-value structure-of-structures
                       set-of-sets empty-struc non-empty-struc unary-pred binary-pred
                       tertiary-pred)
  isa (repr-concept anything category)
  is-range-of (random-choose good-choose best-choose and or the-second-of the-first-of
                             first-ele second-ele third-ele all-but-first all-but-second
                             all-but-third last-ele all-but-last proj1 proj2 proj-1-of-3
                             proj-2-of-3 proj-3-of-3 identity1 implies ord-struc-equal)
  in-domain-of (equal eq and or the-second-of the-forst-of always-t always-nil
                      constant-binary-pred always-t-2 always-nil-2 constant-unary-pred
                      undefined-pred struc-insert struc-delete set-insert set-delete
                      list-insert list-delete list-delete-1 bag-insert bag-delete
                      bag-delete-1 mult-ele-struc-delete-1 o-set-insert o-set-delete member
                      memb proj1 proj2 proj-1-of-3 proj-2-of-3 proj-3-of-3 identity1 not
                      implies mult-ele-struc-insert)
  fast-defn (lambda (x)
              (declare (ignore x))
              t)
  examples (and or the-first-of the-second-of square divisors-of multiply-add successor
                random-choose random-subset good-choose best-choose best-subset
                good-subset equal ieqp eq ileq igeq ilessp igreaterp los1 los2 los3
                los4 los5 los6 los7 win1 t nil proto-conjec 1 3 5 7 9 11 13 15 17
                19 21 23 25 27 29 31 33 35 37 39 41 43 45 47 49 51 53 55 57 59 61
                63 65 67 69 71 73 75 77 79 81 83 85 6 28 if-about-to-work-on-task
                applics if-finished-working-on-task isa if-truly-relevant sub-slots
                if-parts if-potentially-relevant examples data-type english worth
                inverse creditors generalizations specializations then-add-to-agenda
                then-compute then-connjecture abbrev then-define-new-concepts
                then-modify-slots then-print-to-user then-parts super-slots if-task-parts
                format dont-copy double-check generator if-working-on-task is-range-of
                to-delete-1 alg fast-defn recursive-defn unitized-defn fast-alg
                iterative-alg recursive-alg unitized-alg iterative-defn to-delete
                applic-generator arity non-examples compiled-defn elim-slots
                in-domain-of domain range indirect-applics direct-applics defn
                sib-slots transpose then-delete-old-concepts subsumes subsumed-by
                overall-record then-print-to-user-failed-record
                then-add-to-agenda-failed-record then-delete-old-concepts-failed-record
                then-define-new-concepts-failed-record then-conjecture-failed-record
                then-modify-slots-failed-record then-compute-failed-record
                then-print-to-user-record then-add-to-agenda-record
                then-delete-old-concepts-record then-define-new-concepts-record
                then-conjecture-record then-modify-slots-record then-compute-record
                record-for failed-record-for record failed-record h1 h5 h6 h3 h4 h7 h8
                h9 h10 h11 h2 h12 h-avoid h-avoid-2 h-avoid-3 h13 h14 h15 h16 h17 h18
                h19 h-avoid-2-and h-avoid-3-first h-avoid-if-working h5-criterial h5-good
                h19-criterial set heuristic anything math-concept slot math-obj
                nnumber unit prime-num conjecture repr-concept even-num task math-op
                odd-num perf-num perf-square op set-of-numbers set-op unit-op num-op
                criterial-slot pred math-pred bit non-criterial-slot hind-sight-rule
                unary-unit-op record-slot h20 conjectures h21 conjecture-about
                structure category struc-equal set-equal subsetp constant-pred
                always-t always-nil constant-binary-pred always-t-2 always-nil-2
                constant-unary-pred compose undefined-pred struc-insert struc-op
                struc-delete set-insert set-delete list-op list list-insert list-delete
                list-delete-1 bag bag-op bag-insert bag-delete bag-delete-1 mult-ele-struc
                mult-ele-struc-op mult-ele-struc-delete-1 o-set o-set-insert o-set-op
                o-set-delete no-mult-ele-struc ord-struc un-ord-struc nec-defn suf-defn
                o-set-equal bag-equal list-equal ord-struc-op ord-struc-equal set-intersect
                set-union struc-intersect list-intersect o-set-intersect bag-intersect
                struc-union o-set-union list-union bag-union struc-difference
                set-difference list-difference o-set-difference bag-difference coalesce
                type-of-structure unary-op parallel-replace each-element-is-a binary-op
                parallel-replace-2 repeat tertiary-op repeat2 parallel-join
                parallel-join-2 o-pair pair reverse-o-pair first-ele second-ele third-ele
                all-but-first all-but-second all-but-third last-ele all-but-last member
                memb proj1 proj2 proj-1-of-3 proj-2-of-3 proj-3-of-3 identity1 restrict
                inverted-op invert-op set-of-o-pairs relation logic-op not implies atom
                truth-value structure-of-structures set-of-sets empty-struc
                non-empty-struc undefined lower-arity higher-arity unary-pred
                binary-pred tertiary-pred pred-cat-by-nargs op-cat-by-narts extensions
                restrictions interestingness h22 more-interesting less-interesting
                int-examples h23 h24 why-int rarity is-a-int h25 h26 h27 28 h29
                mult-ele-struc-insert int-applics english-1 restric-random-subset-3)
  rarity (1 12 0))

(defunit applic-generator
  worth 600
  isa (slot criterial-slot repr-concept anything)
  data-type lisp-fn
  format (applic-gen-init applic-gen-build applic-gen-args))

(defunit applics
  worth 338
  isa (slot non-criterial-slot repr-concept anything)
  format ((situation resultant-units directness)
          (situation resultant-units directness)
          etc.)
  data-type io-pair
  sub-slots (direct-applics indirect-applics int-applics)
  double-check t
  dont-copy t
  more-interesting (int-applics))

(defunit arity
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  data-type number)

(defunit best-choose
  worth 500
  isa (math-concept math-op op set-op anything struc-op unary-op)
  fast-alg #'best-choose
  domain (set)
  range (anything)
  generalizations (random-choose good-choose)
  elim-slots (applics)
  arity 1)

(defunit best-subset
  worth 500
  isa (math-concept math-op op set-op anything struc-op unary-op)
  fast-alg #'best-subset
  domain (set)
  range (set)
  generalizations (random-subset good-subset)
  elim-slots (applics)
  arity 1
  rarity (0.95 19 1))

(defunit bit
  is-range-of (equal ieqp eq ileq igeq ilessp igreaterp struc-equal set-equal subsetp
                     always-t always-nil constant-binary-pred always-t-2 always-nil-2
                     constant-unary-pred o-set-equal bag-equal list-equal member memb not)
  worth 500
  isa (math-concept math-obj anything category)
  examples (t nil)
  fast-defn (lambda (b)
              (or (eq b nil)
                  (eq b t)))
  generalizations (anything))

(defunit category
  worth 500
  isa (category anything repr-concept)
  examples (set heuristic anything math-concept slot math-obj nnumber unit prime-num
                conjecture repr-concept even-num task math-op odd-num perf-num
                perf-square op set-of-numbers set-op unit-op num-op criterial-slot pred
                math-pred bit non-criterial-slot hind-sight-rule unary-unit-op record-slot
                structure category constant-pred struc-op list-op list bag bag-op
                mult-ele-struc mult-ele-struc-op o-set o-set-op no-mult-ele-struc ord-struc
                un-ord-struc ord-struc-op type-of-structure unary-op binary-op tertiary-op
                o-pair pair inverted-op set-of-o-pairs relation logic-op atom truth-value
                structure-of-structures set-of-sets empty-struc non-empty-struc unary-pred
                binary-pred tertiary-pred pred-cat-by-nargs op-cat-by-nargs)
  specializations (type-of-structure pred-cat-by-nargs op-cat-by-nargs)
  interestingness (interp3 'h24 u 'why-int))

(defunit compiled-defn
  super-slots (defn)
  worth 600
  isa (slot criterial-slot repr-concept anything)
  data-type compiled-lisp-code)

(defunit compose
  isa (math-concept math-op op anything binary-op)
  worth 990
  arity 2
  domain (op op)
  range (op)
  elim-slots (applics)
  fast-alg (lambda (f g)
             (cond ((and (range f)
                         (domain g)
                         (is-a-kind-of (car (range f))
                                       (car (domain g))))
                    (let ((fargs (mapcar #'the-second-of
                                         (domain f)
                                         '(u v w x y z z2 z3 z4 z5)))
                          (gargs (mapcar #'the-second-of
                                         (cdr (domain g))
                                         '(a b c d e f g h i j k)))
                          (nam (create-unit (pack* g '-o- f))))
                      (put nam 'isa (set-diff (isa g)
                                              (examples 'op-cat-by-nargs)))
                      (put nam 'worth (average-worths 'compose (average-worths f g)))
                      (put nam 'arity (+ (length fargs)
                                         (length gargs)))
                      (put nam 'domain (append (copy (domain f))
                                               (cdr (domain g))))
                      (put nam 'range (copy (range g)))
                      (put nam 'unitized-alg `(lambda ,(nconc (copy fargs) (copy gargs))
                                                (run-alg ,g (run-alg ,f ,@fargs) ,@gargs)))
                      (put nam 'elim-slots '(applics))
                      (put nam 'creditors '(compose))
                      (put nam 'isa (append (isa nam)
                                            (subset (examples 'op-cat-by-nargs)
                                                    (lambda (pc)
                                                      (run-defn pc nam)))))
                      (add-inv nam)
                      nam))
                   (t ;; ORIG: we should check for cases where f could sub for other than the first arg of g
                    'failed)))
  rarity (0.3612903 56 99))

(defunit conjecture
  worth 500
  examples (proto-conjec)
  isa (repr-concept anything category)
  generalizations (anything))

(defunit conjecture-about
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  data-type unit
  double-check t
  dont-copy t
  inverse (conjectures))

(defunit conjectures
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  data-type conjecture
  double-check t
  dont-copy t
  inverse (conjecture-about))

(defunit constant-binary-pred
  worth 500
  isa (op pred anything unary-op math-op binary-pred)
  arity 2
  domain (anything)
  range (bit)
  elim-slots (applics)
  specializations (always-t2 always-nil-2))

(defunit constant-pred
  generalizations (op pred anything)
  worth 500
  isa (anything category math-op repr-concept)
  examples (always-t always-nil always-t-2 always-nil-2))

(defunit constant-unary-pred
  worth 500
  isa (op pred anything unary-op math-op unary-pred)
  arity 1
  domain (anything)
  range (bit)
  elim-slots (applics)
  specializations (always-t always-nil))

(defunit creditors
  to-delete-1 (lambda (u1 p u2)
                (declare (ignore p))
                ;; ORIG: U1 is on the P property of unit U2, and is now being deleted. We must remove accreditation of U2 from the Applics slot of U1
                ;; TODO - but P is unused in the original code, too? or is that another dynamic binding? or it's legitimately ignored, as we're removing effects of stuff being deleted from P, but not ever accessing it ourselves?
                (rem1prop u1 'applics (car (some (applics u1)
                                                 (lambda (a)
                                                   (eq (caadr a) u2))))))
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  data-type unit)

(defunit criterial-slot
  isa (repr-concept math-concept anything category)
  worth 500
  generalizations (slot anything repr-concept)
  examples (alg applic-generator compiled-defn data-type defn domain elim-slots
                fast-alg fast-defn generator if-about-to-work-on-task
                if-finished-working-on-task if-parts if-potentially-relevant
                if-task-parts if-truly-relevant if-working-on-task iterative-alg
                iterative-defn non-examples recursive-alg recursive-defn
                then-add-to-agenda then-compute then-conjecture
                then-define-new-concepts then-modify-slots then-parts
                then-print-to-user to-delete to-delete-1 unitized-alg unitized-defn
                then-delete-old-concepts nec-defn suf-defn each-element-is-a))

(defunit data-type
  worth 600
  isa (slot criterial-slot repr-concept anything)
  data-type data-type
  double-check t)

(defunit defn
  worth 600
  isa (slot criterial-slot repr-concept anything)
  data-type list-pred
  sub-slots (compiled-defn fast-defn iterative-defn recursive-defn unitized-defn suf-defn nec-defn)
  specializations (nec-defn suf-defn))

(defunit direct-applics
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  format ((situation resultant-units directness)
          (situation resultant-units directness)
          etc.)
  data-type io-pair
  super-slots (applics)
  double-check t
  dont-copy t)

(defunit divisors-of
  worth 500
  isa (math-concept math-op op num-op anything unary-op)
  fast-alg (lambda (n)
             (sort (loop for i from 1
                         ;; OPTIMIZATION - hoist calculation
                         until (> (square i) n)
                         ;; OPTIMIZATION - cache computation between divides & floor
                         when (divides i n)
                           collect i
                           and
                             collect (floor n i))
                   #'<))
  iterative-alg (lambda (n)
                  (loop for i from 1 to n
                        when (divides i n)
                          collect i))
  domain (nnumber)
  range (set-of-numbers)
  elim-slots (applics)
  arity 1)

(defunit domain
  worth 600
  isa (slot criterial-slot repr-concept anything)
  data-type unit
  inverse (in-domain-of))

(defunit dont-copy
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  data-type bit)

(defunit double-check
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  data-type bit)

(defunit eq
  worth 507
  isa (math-concept math-op op math-pred pred anything binary-op binary-pred)
  fast-alg #'eq
  arity 2
  domain (anything anything)
  range (bit)
  generalizations (equal)
  elim-slots (applics)
  is-a-int (binary-pred)
  rarity (0.1 1 9))

(defunit equal
  worth 502
  isa (math-concept math-op op math-pred pred anything binary-op binary-pred)
  fast-alg #'equal
  arity 2
  domain (anything anything)
  range (bit)
  specializations (ieqp eq struc-equal set-equal o-set-equal bag-equal list-equal)
  elim-slots (applics))

(defunit elim-slots
  worth 600
  isa (slot criterial-slot repr-concept anything)
  data-type slot
  double-check t)

(defunit english
  worth 304
  isa (slot non-criterial-slot repr-concept anything)
  data-type text)

(defunit even-num
  generalizations (nnumber anything)
  worth 800
  unitized-defn (lambda (n)
                  (run-alg 'divides 2 n))
  isa (math-concept math-obj anything category)
  fast-defn (lambda (n)
              (and (fixp n)
                   ;; OPTIMIZATION - just test low bit
                   (divides 2 n)))
  elim-slots (examples))

(defunit examples
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  inverse (isa)
  data-type unit
  double-check t
  dont-copy t
  sub-slots (int-examples)
  more-interesting (int-examples))

(defunit failed-record
  worth 600
  isa (slot non-criterial-slot repr-concept anything)
  double-check t
  data-type slot
  inverse (failed-record-for))

(defunit failed-record-for
  worth 600
  isa (slot non-criterial-slot repr-concept anything)
  double-check t
  data-type slot
  inverse (failed-record))

(defunit fast-alg
  super-slots (alg)
  isa (slot criterial-slot repr-concept anything)
  worth 600
  data-type lisp-fn
  dont-copy t)

(defunit fast-defn
  super-slots (defn)
  worth 600
  isa (slot criterial-slot repr-concept anything)
  data-type lisp-pred)

(defunit format
  worth 400
  isa (slot non-criterial-slot repr-concept anything)
  data-type data-type)

(defunit generalizations
  worth 306
  isa (slot non-criterial-slot repr-concept anything)
  sub-slots (super-slots extensions)
  inverse (specializations)
  data-type unit
  double-check t)

(defunit generator
  worth 600
  isa (slot criterial-slot repr-concept anything)
  data-type lisp-fn
  format (gen-init gen-build gen-args))

(defunit good-choose
  worth 500
  isa (math-concept math-op op set-op anyting struc-op unary-op)
  fast-alg #'good-choose
  domain (set)
  range (anything)
  generalizations (random-choose)
  specializations (best-choose)
  elim-slots (applics)
  arity 1)

(defunit good-subset
  worth 500
  isa (math-concept math-op op set-op anything struc-op unary-op)
  fast-alg #'good-subset
  domain (set)
  range (set)
  generalizations (random-subset)
  specializations (best-subset)
  elim-slots (applics)
  arity 1)

(defunit heuristic
  worth 900
  examples (h1 h5 h6 h3 h4 h7 h8 h9 h10 h11 h2 h12 h-avoid h-avoid-2 h-avoid-3 h13 h14
               h15 h16 h17 h18 h19 h-avoid-2-and h-avoid-3-first h-avoid-if-working
               h5-criterial h5-good h19-criterial h20 h21 h22 h23 h24 h25 h26 h27
               ;; TODO - H1-6 is referenced twice in EUR, but not found anywhere
               h28 h20 h1-6)
  isa (repr-concept anything category)
  generalizations (op anything repr-concept)
  specializations (hind-sight-rule))

(defunit hind-sight-rule
  worth 900
  isa (repr-concept anything category)
  generalizations (op heuristic anything repr-concept)
  abbrev ("Heuristic rules for learning from bitter experiences")
  examples (h12 h13 h14))

(defunit ieqp
  worth 500
  isa (math-concept math-op op math-pred pred anything num-op binary-op binary-pred)
  ;; OPTIMIZATION - a version with fixnum declarations, and fixed arity?
  fast-alg #'=
  arity 2
  domain (nnumber nnumber)
  range (bit)
  generalizations (equal ileq igeq)
  elim-slots (applics)
  is-a-int (binary-pred)
  rarity (0.1 1 9))

(defunit igeq
  worth 509
  isa (math-concept math-op op math-pred pred anything num-op binary-op binary-pred)
  fast-alg #'>= ;; OPTIMIZATION - fixed arity, fixnum decls
  arity 2
  domain (nnumber nnumber)
  range (bit)
  specializations (ieqp igreaterp)
  transpose (ileq)
  elim-slots (applics))

(defunit igreaterp
  worth 501
  isa (math-concept math-op op math-pred pred anything num-op binary-op binary-pred)
  fast-alg #'> ;; OPTIMIZATION
  arity 2
  domain (nnumber nnumber)
  range (bit)
  generalizations (igeq)
  transpose (ilessp)
  elim-slots (applics))

(defunit ileq
  worth 500
  isa (math-concept math-op op math-pred pred anythign num-op binary-op binary-pred)
  fast-alg #'<=
  arity 2
  domain (nnumber nnumber)
  range (bit)
  specializations (ieqp ilessp)
  transpose (igeq)
  elim-slots (applics))

(defunit ilessp
  worth 500
  isa (math-concept math-op op math-pred pred anything num-op binary-op binary-pred)
  fast-alg #'<
  arity 2
  domain (nnumber nnumber)
  range (bit)
  generalizations (ileq)
  transpose (igreaterp)
  elim-slots (applics))

(defunit if-about-to-work-on-task
  worth 600
  isa (slot criterial-slot repr-concept anything)
  super-slots (if-parts if-task-parts)
  data-type lisp-pred)

(defunit if-finished-working-on-task
  worth 600
  isa (slot criterial-slot repr-concept anything)
  super-slots (if-task-parts if-parts)
  data-type lisp-pred)

(defunit if-parts
  worth 600
  sub-slots (if-potentially-relevant if-truly-relevant if-about-to-work-on-task
                                     if-working-on-task if-finished-working-on-task)
  isa (slot criterial-slot repr-concept anything)
  data-type lisp-pred)

(defunit if-potentially-relevant
  worth 600
  isa (slot criterial-slot repr-concept anything)
  super-slots (if-parts)
  data-type lisp-pred)

(defunit if-task-parts
  worth 600
  isa (slot criterial-slot repr-concept anything)
  sub-slots (if-about-to-work-on-task if-working-on-task if-finished-working-on-task)
  data-type lisp-pred)

(defunit if-truly-relevant
  worth 600
  isa (slot criterial-slot repr-concept anything)
  super-slots (if-parts)
  data-type (lisp-pred))

(defunit if-working-on-task
  worth 600
  isa (slot criterial-slot repr-concept anything)
  super-slots (if-parts if-task-parts)
  data-type lisp-pred)

(defunit in-domain-of
  inverse (domain)
  isa (slot non-criterial-slot repr-concept anything)
  worth 300
  data-type unit)

(defunit indirect-applics
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  format ((situation resultant-units directness)
          (situation resultant-units directness)
          etc.)
  data-type io-pair
  super-slots (applics)
  double-check t
  dont-copy t)

(defunit inverse
  worth 600
  isa (slot non-criterial-slot repr-concept anything)
  inverse (inverse)
  data-type slot
  double-check t)

(defunit isa
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  inverse (examples)
  data-type unit
  double-check t)

(defunit is-range-of
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  data-type unit
  inverse (range))

(defunit iterative-alg
  super-slots (alg)
  isa (slot criterial-slot repr-concept anything)
  worth 600
  data-type lisp-fn)

(defunit iterative-defn
  super-slots (defn)
  worth 600
  isa (slot criterial-slot repr-concept anything)
  data-type lisp-red)

(defunit math-concept
  generalizations (anything)
  worth 500
  examples (nnumber prime-num perf-num perf-square odd-num even-num square
                    divisors-of multiply add successor set set-of-numbers
                    random-choose random-subset good-choose best-choose best-subset
                    good-subset bit equal ieqp eq ileq igeq ilessp igreaterp
                    slot unit criterial-slot non-criterial-slot math-concept
                    math-obj math-op math-pred num-op set-op los1 los2 los3 los4
                    los5 los6 los7 win1 record-slot structure struc-equal
                    set-equal subsetp compose struc-insert struc-op struc-delete
                    set-insert set-delete list-op list list-insert list-delete
                    list-delete-1 bag bag-op bag-insert bag-delete bag-delete-1
                    mult-ele-struc mult-ele-struc-op mult-ele-struc-delete-1 o-set
                    o-set-insert o-set-op o-set-delete no-mult-ele-struc ord-struc
                    un-ord-struc o-set-equal bag-equal list-equal ord-struc-op
                    ord-struc-equal set-intersect set-union struc-intersect
                    list-intersect o-set-intersect bag-intersect struc-union
                    o-set-union list-union bag-union struc-difference set-difference
                    list-difference o-set-difference bag-difference coalesce
                    parallel-replace parallel-replace-2 repeat repeat2
                    parallel-join parallel-join-2 o-pair pair reverse-o-pair first-ele
                    second-ele third-ele all-but-first all-but-second all-but-third
                    last-ele all-but-last member memb proj1 proj2 proj-1-of-3
                    proj-2-of-3 proj-3-of-3 identity1 restrict inverted-op invert-op
                    set-of-o-pairs relation logic-op structure-of-structures
                    set-of-sets empty-struc non-empty-struc mult-ele-struc-insert
                    restric-random-subset-3)
  specializations (math-op math-obj set-op unit-op num-op math-pred struc-op list-op
                           bag-op mult-ele-struc-op o-set-op ord-struc-op inverted-op
                           logic-op)
  isa (math-concept math-obj anything category))

(defunit math-obj
  generalizations (math-concept anything)
  worth 500
  examples (nnumber prime-num perf-num per-square odd-num even-num set set-of-numbers bit
                    math-concept num-op set-op math-pred math-obj math-op los1 los2 los3
                    los4 los5 los6 los7 win1 structure struc-op list-op list bag
                    bag-op mult-ele-struc mult-ele-struc-op o-set o-set-op no-mult-ele-struc
                    ord-struc un-ord-struc ord-struc-op o-pair pair inverted-op
                    set-of-o-pairs relation logic-op structure-of-structures set-of-sets
                    empty-struc non-empty-struc truth-value)
  isa (math-concept math-obj anything category))

(defunit math-op
  generalizations (math-concept op anything)
  worth 500
  examples (divisors-of square multiply add successor random-choose random-subset
                        good-choose best-choose best-subset good-subset equal ieqp eq
                        ileq igeq ilessp igreaterp and or the-firsrt-of the-second-of
                        struc-equal set-equal subsetp compose struc-insert struc-delete
                        set-insert set-delete list-insert list-delete list-delete-1
                        bag-insert bag-delete bag-delete-1 mult-ele-struc-delete-1 o-set-insert
                        o-set-delete o-set-equal bag-equal list-equal ord-struc-equal
                        set-intersection set-union struc-intersect list-intersect
                        o-set-intersect bag-intersect struc-union o-set-union list-union
                        bag-union struc-difference set-difference list-difference
                        o-set-difference bag-difference coalesce prallel-replace
                        parallel-replace-2 repeat repeat2 parallel-join parallel-join2
                        reverse-o-pair first-ele second-ele third-ele all-but-first
                        all-but-second all-but-third last-ele all-but-last member memb proj1
                        proj2 proj-1-of-3 proj-2-of-3 proj-3-of-3 identity1 restrict invert-op
                        not implies always-nil always-nil-2 always-t always-t-2
                        constant-binary-pred constant-pred constant-unary-pred
                        undefined-pred mult-ele-struc-insert restric-random-subset-3)
  isa (math-concept math-obj anything category)
  specializations (set-op unit-op num-op struc-op list-op bag-op mult-ele-struc-op o-set-op
                          ord-struc-op inverted-op logic-op))

(defunit math-pred
  generalizations (math-concept op pred anything)
  worth 500
  isa (math-concept math-obj anything category)
  examples (equal ieqp eq ileq igeq ilessp igreaterp and or the-first-of the-second-of
                  struc-equal set-equal subsetp o-set-equal bag-equal list-equal member
                  memb not implies))

(defunit multiply
  worth 500
  isa (math-concept math-op op num-op anything binary-op)
  fast-alg (lambda (x y)
             (* x y))
  recursive-alg (lambda (x y)
                  (cond ((eq x 0) 0)
                        ((eq x 1) y)
                        (t (run-alg 'add y (run-alg 'multiply (1- x) y)))))
  unitized-alg (lambda (x y)
                 (cond ((eq x 0) 0)
                       ((eq x 1) y)
                       (t (run-alg 'add y (run-alg 'multiply (1- x) y)))))
  iterative-alg (lambda (x y)
                  (loop for i from 1 to x
                        sum y))
  arity 2
  domain (nnumber nnumber)
  range (nnumber)
  elim-slots (applics))

(defunit nnumber
  worth 500
  isa (math-concept math-obj anything category)
  specializations (prime-num perf-num perf-square odd-num even-num)
  generator ((0) (1+) (old))
  fast-defn #'fixp
  in-domain-of (divisors-of multiply add successor square ieqp ileq igeq ilessp igreaterp)
  is-range-of (multiply add successor)
  elim-slots (examples)
  generalizations (anything)
  rarity (0 1 3))

(defunit non-criterial-slot
  isa (repr-concept math-concept anything category)
  worth 500
  generalizations (slot anything repr-concept)
  examples (abbrev applics arity creditors direct-applics dont-copy
                   double-check english examples format generalizations
                   in-domain-of indirect-applics isa is-range-of range sib-slots
                   specializations sub-slots super-slots transpose worth
                   inverse subsumes subsumed-by overall-record
                   then-print-to-user-failed-record then-add-to-agenda-failed-record
                   then-delete-old-concepts-failed-record
                   then-define-new-concepts-failed-record
                   then-conjecture-failed-record then-modify-slots-failed-record
                   then-compute-failed-record then-print-to-user-record
                   then-add-to-agenda-record then-delete-old-concepts-record
                   then-define-new-concepts-record then-conjecture-record
                   then-modify-slots-record then-compute-record record-for
                   failed-record-for record failed-record conjectures
                   conjecture-about lower-arity higher-arity extensions
                   restrictions interestingness more-interesting
                   less-interesting int-examples why-int rarity is-a-int
                   int-applics))

(defunit non-examples
  worth 600
  isa (slot criterial-slot repr-concept anything)
  data-type unit
  double-check t
  dont-copy t)

(defunit num-op
  generalizations (math-concept op math-op anything)
  worth 500
  isa (math-concept math-obj anything category)
  abbrev ("Numeric Operations")
  examples (divisors-of square multiply add successor ieqp ileq igeq ilessp igreaterp))

(defunit or
  worth 500
  isa (op pred math-op math-pred anything binary-op logic-op binary-pred)
  fast-alg (lambda (x y)
             (or x y))
  arity 2
  domain (anything anything)
  range (anything)
  elim-slots (applics)
  specializations (the-first-of the-second-of and))

(defunit odd-num
  generalizations (nnumber anything)
  worth 700
  unitized-defn (lambda (n)
                  ;; BUGFIX - missed quote on DIVIDES
                  (not (run-alg 'divides 2 n)))
  isa (math-concept math-obj anything category)
  fast-defn (lambda (n)
              (and (fixp n)
                   (oddp n)))
  elim-slots (examples))

(defunit op
  worth 500
  isa (repr-concept anything category)
  specializations (math-op heuristic set-op unit-op num-op pred math-pred hind-sight-rule
                           constant-pred struc-op list-op bag-op mult-ele-struc-op o-set-op
                           ord-struc-op unary-op binary-op tertiary-op inverted-op logic-op
                           unary-pred binary-pred tertiary-pred)
  examples (random-choose random-subset good-choose-best-choose best-subset good-subset
                          divisors-of square multiply add successor equal ieqp eq ileq
                          igeq ilessp igreaterp h12 h13 h14 h1 h5 h6 h3 h4 h7 h8 h9 h10
                          h11 h2 h-avoid h-avoid-2 h-avoid-3 h15 and or the-second-of the-first-of
                          h19 h-avoid-2-and h-avoid-3-first h-avoid-if-working h5-criterial h5-good
                          h19-criterial h20 h21 struc-equal set-equal subsetp always-t
                          always-nil constant-binary-pred always-t-2 always-nil-2
                          constant-unary-pred compose undefined-pred struc-insert struc-delete
                          set-insert set-delete list-insert list-delete list-delete-1 bag-insert
                          bag-delete bag-delete-1 mult-ele-struc-delete-1 o-set-insert o-set-delete
                          o-set-equal bag-equal list-equal ord-struc-equal set-intersect
                          set-union struc-intersect list-intersect o-set-intersect
                          bag-intersect struc-union o-set-union list-union bag-union
                          struc-difference set-difference list-difference o-set-difference
                          bag-difference coalesce parallel-replace parallel-replace-2 repeat
                          repeat2 parallel-join parallel-join-2 reverse-o-pair first-ele
                          second-ele third-ele all-but-fist all-but-second all-but-third last-ele
                          all-but-last member memb proj1 proj2 proj-1-of-3 proj-2-of-3 proj-3-of-3
                          idenitity1 restrict invert-op not implies h22 h23 h24 h29 h16 h17
                          h18 h25 h26 h27 h28 mult-ele-struc-insert h1-6)
  generalizations (anything)
  in-domain-of (compose coalesce restrict invert-op)
  is-range-of (compose coalesce restrict))

(defunit overall-record
  worth 300
  isa (slot non-criterial-slot repr-concept anything record-slot)
  data-type dotted-pair
  dont-copy t)

(defunit perf-num
  generalizations (nnumber anything)
  worth 800
  unitized-defn (lambda (n)
                  (eq (run-alg 'double n)
                      (apply #'+ (run-alg 'divisors-of n))))
  isa (math-concept math-obj anything category)
  iterative-defn (lambda (n)
                   (and (fixp n)
                        (eq (1- n)
                            (loop for i from 2 to (1- n)
                                  sum (cond ((divides i n) i)
                                            (t 0))))))
  elim-slots nil
  non-examples (0 1)
  examples (6 28))

(defunit perf-square
  generalizations (nnumber anything)
  worth 950
  is-range-of (square)
  isa (math-concept math-obj anything category)
  elim-slots (examples))

(defunit pred
  generalizations (op anything)
  worth 500
  isa (repr-concept anything category)
  abbrev ("Boolean predicates")
  specializations (math-pred constant-pred unary-pred binary-pred tertiary-pred)
  examples (equal ieqp eq ileq igeq ilessp igreaterp and or the-second-if the-first-of
                  struc-equal set-equal subsetp always-t always-nil constant-binary-pred
                  always-t-2 always-nil-2 constant-unary-pred undefined-pred o-set-equal
                  bag-equal list-equal member memb not implies))

(defunit prime-num
  generalizations (nnumber anything)
  worth 950
  unitized-defn (lambda (n)
                  (run-defn (run-alg 'divisors-of n)
                            'doubleton))
  isa (math-concept math-obj anything category)
  iterative-defn (lambda (n)
                   (and (fixp n)
                        (eq 0 (loop for i from 2 to (1- n)
                                    sum (cond ((divides i n) i)
                                              (t 0))))))
  fast-defn (lambda (n)
              (and (fixp n)
                   (loop for i from 2 to (isqrt n)
                         never (divides i n))))
  non-examples (0 1)
  elim-slots (examples))

(defunit proto-conjec
  worth 802
  isa (conjecture repr-concept anything))

(defunit random-choose
  worth 507
  isa (math-concept math-op op set-op anything struc-op unary-op)
  fast-alg #'random-choose
  domain (set)
  range (anything)
  specializations (good-choose best-choose)
  elim-slots (applics)
  arity 1)

(defunit random-subset
  worth 520
  isa (math-concept math-op op set-op anything struc-op unary-op)
  fast-alg #'random-subset
  domain (set)
  range (set)
  specializations (best-subset good-subset)
  elim-slots (applics)
  arity 1
  rarity (0.4065041 50 73))

(defunit range
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  data-type unit
  inverse (is-range-of))

(defunit record
  worth 600
  isa (slot non-criterial-slot repr-concept anything)
  double-check t
  data-type slot
  inverse (record-for))

(defunit record-for
  worth 600
  isa (slot non-criterial-slot repr-concept anything)
  double-check t
  data-type slot
  inverse (record))

(defunit record-slot
  isa (repr-concept math-concept anything category)
  worth 500
  generalizations (slot anything repr-concept)
  examples (then-compute-record then-compute-failed-record then-modify-slots-record
                                then-modify-slots-failed-record then-conjecture-record
                                then-conjecture-failed-record
                                then-define-new-concepts-record
                                then-define-new-concepts-failed-record
                                then-delete-old-concepts-record
                                then-delete-old-concepts-failed-record
                                then-add-to-agenda-record then-add-to-agenda-failed-record
                                then-print-to-user-record then-print-to-user-failed-record
                                overall-record))

(defunit recursive-alg
  super-slots (alg)
  isa (slot criterial-slot repr-concept anything)
  worth 600
  data-type lisp-fn)

(defunit recursive-defn
  super-slots (defn)
  worth 600
  isa (slot criterial-slot repr-concept anything)
  data-type lisp-pred)

(defunit repr-concept
  generalizations (anything)
  worth 500
  examples (slot unit criterial-slot non-criterial-slot heuristic hind-sight-rule
                 unit-op unary-unit-op repr-concept conjecture task anything pred
                 op proto-conjec abbrev alg applic-generator applics arity
                 compiled-defn creditors data-type defn direct-applics domain
                 dont-copy double-check elim-slots english examples failed-record
                 failed-record-for fast-alg fast-defn format generalizations
                 generator if-about-to-work-on-task if-finished-working-on-task if-parts
                 if-potentially-relevant if-task-parts if-truly-relevant
                 if-working-on-task in-domain-of indirect-applics inverse isa
                 is-range-of iterative-alg iterative-defn non-examples overall-record
                 range record record-for recursive-alg recursive-defn sib-slots
                 specializations sub-slots subsumed-by subsumes super-slots
                 then-add-to-agenda then-add-to-agenda-failed-record
                 then-add-to-agenda-record then-compute then-compute-failed-record
                 then-compute-record then-conjecture then-conjecture-failed-record
                 then-conjecture-record then-define-new-concepts
                 then-define-new-concepts-failed-recored then-define-new-concepts-record
                 then-delete-old-concepts then-delete-old-concepts-failed-record
                 then-delete-old-concepts-record then-modify-slots
                 then-modify-slots-failed-record then-modify-slots-record then-parts
                 then-print-to-user then-print-to-user-failed-record
                 then-print-to-user-record to-delete to-delete-1 transpose unitized-alg
                 unitized-defn worth record-slot conjectures conjecture-about
                 category nec-defn suf-defn type-of-structure unary-op
                 each-element-is-a binary-op tertiary-op atom constant-pred undefined
                 lower-arity higher-arity unary-pred binary-pred tertiary-pred
                 pred-cat-by-nargs op-cat-by-nargs extensions restrictions
                 interestingness more-interesting less-interesting int-examples
                 why-int rarity is-a-int int-applics english-1)
  isa (repr-concept anything category)
  specializations (slot criterial-slot non-criterial-slot unit heuristic hind-sight-rule record-slot))

(defunit set
  worth 500
  isa (math-concept math-obj anything category type-of-structure)
  generator ((nil)
             (get-a-set)
             (old))
  fast-defn (lambda (s)
              (or (eq s nil)
                  (no-repeats-in s)))
  recursive-defn (lambda (s)
                   (cond ((not (consp s))
                          (eq s nil))
                         (t (and (not (member (car s) (cdr s)))
                                 (run-defn 'set (cdr s))))))
  in-domain-of (random-choose random-subset good-choose best-choose best-subset good-subset
                              set-equal subsetp set-insert set-delete set-intersect set-union
                              set-difference)
  is-range-of (random-subset best-subset good-subset set-insert set-delete set-intersect
                             set-union set-difference restric-random-subset-2-1
                             restric-random-subset-1-2)
  generalizations (anything structure bag list no-mult-ele-struc un-ord-struc)
  specializations (o-set empty-struc non-empty-struc)
  rarity (0 2 2)
  elim-slots (examples))

(defunit set-equal
  worth 500
  isa (math-concept math-op op math-pred pred anything struc-op set-op binary-op binary-pred)
  arity 2
  domain (set set)
  range (bit)
  generalizations (equal struc-equal subsetp)
  fast-alg (lambda (s1 s2)
             (cond ((not (eq (length s1)
                             (length s2)))
                    nil)
                   ((equal s1 s2)
                    t)
                   (t (and (is-subset-of s1 s2)
                           (is-subset-of s2 s1)))))
  recursive-alg (lambda (s1 s2)
                  (cond ((and (null s1)
                              (null s2))
                         t)
                        (t (and (consp s1)
                                (consp s2)
                                (member (car s1) s2)
                                (run-alg 'set-equal (cdr s2) (remove (car s1) s2))))))
  unitized-alg (lambda (s1 s2)
                 (and (run-alg 'subsetp s1 s2)
                      (run-alg 'subsetp s2 s1)))
  specializations (o-set-equal)
  is-a-int (binary-pred)
  rarity (0.1 1 9))

(defunit set-of-numbers
  is-range-of (divisors-of)
  isa (math-concept math-obj anything category)
  worth 500
  unitized-defn (lambda (s)
                  (and (run-defn 'set s)
                       (every (lambda (n)
                                (run-defn 'nnumber n))
                              s)))
  fast-defn (lambda (s)
              (and (run-defn 'set s)
                   (every #'numberp s)))
  elim-slots (examples)
  generalizations (anything)
  each-element-is-a nnumber)

(defunit set-op
  generalizations (math-concept op math-op anything struc-op)
  worth 500
  isa (math-concept math-obj anything category)
  abbrev ("Set Operations")
  specializations (unit-op)
  examples (random-choose random-subset good-choose best-choose best-subset good-subset
                          set-insert set-delete set-equal set-intersect set-union set-difference))

(defunit sib-slots
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  inverse (sib-slots)
  data-type slot
  double-check t)

(defunit slot
  isa (repr-concept math-concept anything category)
  worth 530
  examples (if-about-to-work-on-task applics if-finished-working-on-task isa if-truly-relevant
                                     sub-slots if-parts if-potentially-relevant examples
                                     data-type english worth inverse creditors
                                     generalizations specializations then-add-to-agenda
                                     then-compute then-conjecture abbrev
                                     then-define-new-concepts then-modify-slots then-print-to-user
                                     then-parts super-slots if-task-parts format dont-copy
                                     double-check generator if-working-on-task is-range-of
                                     to-delete-1 alg fast-defn recursive-defn unitized-defn
                                     fast-alg iterative-alg recursive-alg unitized-alg
                                     iterative-defn to-delete applic-generator arity
                                     non-examples compiled-defn elim-slots in-domain-of domain
                                     range indirect-applics direct-applics defn sib-slots
                                     transpose then-delete-old-concepts subsumes subsumed-by
                                     overall-record then-print-to-user-failed-record
                                     then-add-to-agenda-failed-record
                                     then-delete-old-concepts-failed-record
                                     then-define-new-concepts-failed-record
                                     then-conjecture-failed-record then-modify-slots-failed-record
                                     then-compute-failed-record then-print-to-user-record
                                     then-add-to-agenda-record then-delete-old-concepts-record
                                     then-define-new-concepts-record then-conjecture-record
                                     then-modify-slots-record then-compute-record record-for
                                     failed-record-for record failed-record conjectures
                                     conjecture-about nec-defn suf-defn each-element-is-a
                                     lower-arity higher-arity extensions restrictions
                                     interestingness more-interesting less-interestingk
                                     int-examples why-int rarity is-a-int int-applics)
  specializations (criterial-slot non-criterial-slot record-slot)
  generalizations (unary-unit-op repr-concept anything))

(defunit specializations
  worth 356
  isa (slot non-criterial-slot repr-concept anything)
  sub-slots (sub-slots restrictions)
  inverse (generalizations)
  data-type unit
  double-check t)

(defunit square
  worth 500
  unitized-alg (lambda (n)
                 (run-alg 'multiply n n))
  isa (math-concept math-op op num-op anything unary-op)
  fast-alg (lambda (n)
             (* n n))
  domain (nnumber)
  range (perf-square)
  elim-slots (applics)
  arity 1
  rarity (1.0 220 0))

(defunit struc-equal
  worth 500
  isa (math-concept math-op op math-pred pred anything binary-op binar-pred)
  arity 2
  domain (structure structure)
  range (bit)
  elim-slots (applics)
  generalizations (equal)
  specializations (set-equal o-set-equal bag-equal list-equal)
  is-a-int (binary-pred)
  rarity (0.02 1 49))

(defunit structure
  worth 500
  isa (math-concept math-obj anything category)
  fast-defn #'listp
  recursive-defn (lambda (s)
                   (cond ((not (consp s))
                          (eq s nil))
                         (t (run-defn 'structure (cdr s)))))
  generalizations (anything)
  specializations (set list bag multi-ele-struc o-set no-mult-ele-struc ord-struc
                       un-ord-struc o-pair pair empty-struc non-empty-struc)
  in-domain-of (struc-equal struc-insert struc-delete struc-intersect struc-union
                            struc-difference member memb)
  is-range-of (struc-insert struc-delete struc-intersect struc-union struc-difference)
  interestingness (some (lambda (p)
                          (and (or (has-high-worth p)
                                   (memb p (int-examples 'unary-pred)))
                               (leq-nn (car (rarity p))
                                       0.3)
                               (set tempdef (defn (car (domain p))))
                               (every tempdef u)
                               (setf tempdef (subset u (lambda (e)
                                                         (run-alg p e))))
                               (setf temp2 (car (some (lambda (p2)
                                                        (and (run-defn (cadr (domain p2)) tempdef)
                                                             (run-alg p2 u tempdef)))
                                                      (ok-bin-preds u))))
                               (cprin1 14 "~%The set of elements of " u
                                       " which satisfy the rare predicate " p
                                       " form a very special subset; namely, there are in relation " temp2
                                       " to the entire structure.~%")
                               (cprin1 40 "    They are, by the way: " tempdef "~%")))
                        (examples 'unary-pred))
  rarity (0 2 2))

(defunit sub-slots
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  inverse (super-slots)
  super-slots (specializations)
  data-type slot
  double-check t)

(defunit subsetp
  worth 500
  isa (math-concept math-op op math-pred pred anything binary-op binary-pred)
  arity 2
  domain (set set)
  range (bit)
  elim-slots (applics)
  specializations (set-equal o-set-equal)
  recursive-alg (lambda (s1 s2)
                  (cond ((null s1)
                         t)
                        (t (and (consp s1)
                                (member (car s1) s2)
                                (run-alg 'subsetp (cdr s1) s2)))))
  fast-alg #'is-subset-of)

(defunit subsumed-by
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  inverse (subsumes)
  data-type unit
  double-check t)

(defunit subsumes
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  data-type unit
  double-check t
  inverse (subsumed-by))

(defunit successor
  worth 500
  isa (math-concept math-op op num-op anything unary-op)
  ;; TODO - this originally was (LAMBDA (X Y) (ADD1 X Y)) for some reason? makes no sense
  fast-alg (lambda (x)
             (1+ x))
  domain (nnumber)
  range (nnumber)
  elim-slots (applics)
  arity 1)

(defunit super-slots
  worth 300
  inverse (sub-slots)
  isa (slot non-criterial-slot repr-concept anything)
  super-slots (generalizations)
  data-type slot
  double-check t)

(defunit task
  worth 500
  format (priority-value unit-name slot-name reasons misc-args)
  isa (repr-concept anything category)
  generalizations (anything))

(defunit the-first-of
  worth 500
  isa (op pred math-op math-pred anything binary-op logic-op binary-pred)
  fast-alg (lambda (x y)
             (declare (ignore y))
             x)
  arity 2
  domain (anything anything)
  range (anything)
  elim-slots (applics)
  specializations (and)
  generalizations (or)
  rarity (1.0 42 0))

(defunit the-second-of
  worth 500
  isa (op pred math-op path-pred anyting binary-op logic-op binary-pred)
  fast-alg (lambda (x y)
             (declare (ignore x))
             y)
  arity 2
  domain (anything anything)
  range (anything)
  elim-slots (applics)
  specializations (and)
  generalizations (or))

(defunit then-add-to-agenda
  worth 600
  isa (slot criterial-slot repr-concept anything)
  super-slots (then-parts)
  data-type lisp-fn
  failed-record (then-add-to-agenda-failed-record)
  record (then-add-to-agenda-record))

(defunit then-add-to-agenda-failed-record
  worth 300
  isa (slot non-criterial-slot repr-concept record-slot anything)
  data-type dotted-pair
  failed-record-for (then-add-to-agenda)
  dont-copy t)

(defunit then-add-to-agenda-record
  worth 300
  isa (slot non-criterial-slot repr-concept record-slot anything)
  data-type dotted-pair
  record-for (then-add-to-agenda)
  dont-copy t)

(defunit then-compute
  worth 600
  isa (slot criterial-slot repr-concept anything)
  super-slots (then-parts)
  data-type lisp-fn
  failed-record (then-compute-failed-record)
  record (then-compute-record))

(defunit then-compute-failed-record
  worth 300
  isa (slot non-criterial-slot repr-concept record-slot anything)
  data-type dotted-pair
  failed-record-for (then-compute)
  dont-copy t)

(defunit then-compute-record
  worth 300
  isa (slot-non-criterial-slot repr-concept record-slot anything)
  data-type dotted-pair
  record-for (then-compute)
  dont-copy t)

(defunit then-conjecture
  worth 600
  isa (slot criterial-slot repr-concept anything)
  super-slots (then-parts)
  data-type lisp-fn
  failed-record (then-conjecture-failed-record)
  record (then-conjecture-record))

(defunit then-conjecture-failed-record
  worth 300
  isa (slot non-criterial-slot repr-concept record-slot anything)
  data-type dotted-pair
  failed-record-for (then-conjecture)
  dont-copy t)

(defunit then-conjecture-record
  worth 300
  isa (slot non-criterial-slot repr-concept record-slot anything)
  data-type dotted-pair
  record-for (then-conjecture)
  dont-copy t)

(defunit then-define-new-concepts
  worth 600
  isa (slot criterial-slot repr-concept anything)
  super-slots (then-partts)
  data-type lisp-fn
  failed-record (then-define-new-concepts-failed-record)
  record (then-define-new-concepts-record))

(defunit then-define-new-concepts-failed-record
  worth 300
  isa (slot non-criterial-slot repr-concept record-slot anything)
  data-type dotted-pair
  failed-record-for (then-define-new-concepts)
  dont-copy t)

(defunit then-define-new-concepts-record
  worth 300
  isa (slot non-criterial-slot repr-concept record-slot anything)
  data-type dotted-pair
  record-for (then-define-new-concepts)
  dont-copy t)

(defunit then-delete-old-concepts
  worth 600
  isa (slot criterial-slot repr-concept anything)
  super-slots (then-parts)
  data-type lisp-fn
  failed-record (then-delete-old-concepts-failed-record)
  record (then-delete-old-concepts-record))

(defunit then-delete-old-concepts-failed-record
  worth 300
  isa (slot non-criterial-slot repr-concept record-slot anything)
  data-type dotted-pair
  failed-record-for (then-delete-old-concepts)
  dont-copy t)

(defunit then-delete-old-concepts-record
  worth 300
  isa (slot non-criterial-slot repr-concept record-slot anything)
  data-type dotted-pair
  record-for (then-delete-old-concepts)
  dont-copy t)

(defunit then-modify-slots
  worth 600
  isa (slot criterial-slot repr-concept anything)
  super-slots (then-parts)
  data-type lisp-fn
  failed-record (then-modify-slots-failed-record)
  record (then-modify-slots-record))

(defunit then-modify-slots-failed-record
  worth 300
  isa (slot non-criterial-slot repr-concept record-slot anything)
  data-type dotted-pair
  failed-record-for (then-modify-slots)
  dont-copy t)

(defunit then-modify-slots-record
  worth 300
  isa (slot non-criterial-slot repr-concept record-slot anything)
  data-type dotted-pair
  record-for (then-modify-slots)
  dont-copy t)

(defunit then-parts
  worth 600
  isa (slot criterial-slot repr-concept anything)
  sub-slots (then-compute then-modify-slots then-conjecture then-define-new-concepts
                          then-delete-old-concepts then-add-to-agenda then-print-to-user)
  data-type lisp-fn)

(defunit then-print-to-user
  worth 600
  isa (slot criterial-slot repr-concept anything)
  super-slots (then-parts)
  data-type lisp-fn
  failed-record (then-print-to-user-failed-record)
  record (then-print-to-user-record))

(defunit then-print-to-user-failed-record
  worth 300
  isa (slot non-criterial-slot repr-concept record-slot anything)
  data-type dotted-pair
  failed-record-for (then-print-to-user)
  dont-copy t)

(defunit then-print-to-user-record
  worth 300
  isa (slot non-criterial-slot repr-concept record-slot anything)
  data-type dotted-pair
  record-for (then-print-to-user)
  dont-copy t)

(defunit to-delete
  worth 600
  isa (slot criterial-slot repr-concept anything)
  data-type lisp-fn)

(defunit to-delete-1
  worth 600
  isa (slot criterial-slot repr-concept anything)
  data-type lisp-fn)

(defunit transpose
  worth 300
  isa (slot non-criterial-slot repr-concept anything)
  data-type unit
  double-check t
  inverse (transpose))

(defunit unary-unit-op
  generalizations (unit-op anything)
  worth 500
  isa (repr-concept anything category)
  abbrev ("Operations performable upon a unit")
  specializations (slot))

(defunit undefined
  is-range-of (undefined-pred)
  worth 100
  isa (anything repr-concept))

(defunit undefined-pred
  worth 100
  isa (op pred anything unary-op math-op unary-pred)
  arity 1
  domain (anything)
  range (undefined)
  elim-slots (applics))

(defunit unit
  isa (repr-concept math-concept anything category)
  worth 500
  generalizations (anything repr-concept))

(defunit unit-op
  generalizations (math-concept op math-op set-op anything)
  worth 500
  isa (repr-concept anything category)
  abbrev ("Operations performable upon a set of units")
  specializations (unary-unit-op))

(defunit unitized-alg
  super-slots (alg)
  isa (slot criterial-slot repr-concept anything)
  worth 600
  data-type lisp-fn)

(defunit unitized-defn
  super-slots (defn)
  worth 600
  isa (slot criterial-slot repr-concept anything)
  data-type lisp-pred)

(defunit worth
  worth 305
  isa (slot non-criterial-slot repr-concept anything)
  data-type number)

;; TODO - what are these?  unfinished?
(defunit los1
  worth 100
  isa (math-obj math-concept anything))

(defunit los2
  worth 100
  isa (math-obj math-concept anything))

(defunit los3
  worth 100
  isa (math-obj math-concept anything))

(defunit los4
  worth 100
  isa (math-obj math-concept anything))

(defunit los5
  worth 100
  isa (math-obj math-concept anything))

(defunit los6
  worth 100
  isa (math-obj math-concept anything))

(defunit los7
  worth 100
  isa (math-obj math-concept anything))

(defunit win1
  worth 100
  isa (math-obj math-concept anything))


;; End of file stuff from EUR, does environmental set up in prep for being executed:
;; Actually, this is exactly what's in EURCOMS at the top of the file, probably an RLL editing mechanism

;; [ADVISE (QUOTE EDITP)
;;      (QUOTE BEFORE)
;;      (QUOTE (OR (STKPOS (QUOTE EU))
;;                 (PRIN1 "
;; WARNING:  ARE YOU SURE YOU REALLY DON'T MEAN 'EU' ??? !!! "]
;; (ADVISE (QUOTE MAKEFILE)
;;      (QUOTE BEFORE)
;;      (QUOTE (CheckElim)))
;; (ADVISE (QUOTE PRINTDEF)
;;      (QUOTE AROUND)
;;      (QUOTE (IF (NUMBERP (FIRSTATOM EXPR))
;;                 THEN
;;                 (RESETVARS (PRETTYFLG)
;;                            (RETURN *))
;;                 ELSE *)))
;; (DECLARE: DOEVAL@COMPILE DONTCOPY

;; (ADDTOVAR GLOBALVARS AbortTask? AddedSome Agenda AreUnits CRLF CSlot CSlotSibs CTask Conjectures 
;;        CreditTo Creditors CurPri CurReasons CurSlot CurSup CurUnit CurVal DeletedUnits ESYSPROPS 
;;        EditpTemp FailureList GCredit GSlot HaveGenl HaveSpec HeuristicAgenda Interp LastEdited 
;;        MaybeFailed MapCycleTime MinPri MoveDefns NUnitSlots NeedGenl NeedSpec NewU NewUnit 
;;        NewUnits NewValue NewValues NotForReal nF nT OldKBPu OldKBPv OldVal OldValue PosCred RArrow 
;;        RCU SPACE SYSPROPS ShorterNam SlotToChange SlotsToChange SlotsToElimInitially Slots 
;;        SpecialNonUnits SynthU TTY TaskNum TempCaches UDiff UndoKill Units UnusedSlots UsedSlots 
;;        UserImpatience Verbosity WarnSlots conjec cprintmp)
;; )
;; (SETQ SYSPROPS (UNION ESYSPROPS SYSPROPS))
;; (ADVISE (QUOTE LOGOUT)
;;      (QUOTE BEFORE)
;;      (QUOTE (DRIBBLE)))
;; (ADVISE (QUOTE LOGOUT)
;;      (QUOTE AFTER)
;;      (QUOTE (SOS)))
;; [AND (NULL (GETD (QUOTE OldPACK*)))
;;      (PUTD (QUOTE OldPACK*)
;;         (GETD (QUOTE PACK*)))
;;      (PUTD (QUOTE PACK*)
;;         (GETD (QUOTE SmartPACK*]
;; (InitializeEurisko)
;; (CPRIN1 0 CRLF "You may call (InitialCheckInv) to ferret out references to now-defunct units" CRLF 
;;      CRLF "Type (Eurisko) when you are ready to start." CRLF CRLF)
;; (DECLARE: DONTEVAL@LOAD DOEVAL@COMPILE DONTCOPY COMPILERVARS 

;; (ADDTOVAR NLAMA EU)

;; (ADDTOVAR NLAML )

;; (ADDTOVAR LAMA SmartPACK* CPRIN1)
;; )
;; (DECLARE: DONTCOPY
;;   (FILEMAP ...))
