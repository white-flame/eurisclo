;; Which slots are derived?
;;  applics
;;  any *-record field
;;  subsumed-by ;; from SUBSUMES
;;  arity ? could be determined from the various lambdas?
;;  worth ? is this adjusted during runtime?

(in-package "EURISCLO")

;; Inter-clause vars used in heuristics
(defvar *fraction*)
(defvar *conjec*)
(defvar *pos-cred*)
(defvar *new-reason*)
(defvar *slot-to-change*) ;; also a key 'slot-to-change in *cur-sup*
(defvar *doomed-u*)
(defvar *credit-to*) ;; also 'credit-to in *cur-sup*
(defvar *creditors*) ;; also a slot name & accessor
(defvar *new-units*) ;; also 'new-units in *task-results* ;; TODO - repeated code patterns with this
(defvar *alg-to-use*)
(defvar *slots-to-change*)
(defvar *old-value*)
(defvar *new-value*) ;; not to be confused with *new-values* and 'new-values on *task-results*
(defvar *domain-tests*) ;; TODO - had weird dynamic scope on a then-compute handler. Investigate.
(defvar *defn-to-use*) ;; TODO - only used in h9
(defvar *op-to-use*) ;; TODO - only used in h10
(defvar *ops-to-use*) ;; TODO - only used in h15
(defvar *res-u*) ;; TODO - only used in h21, but also never declared in EUR
(defvar *rule-cycle-time*) ;; TODO - only ever written once, never read, even in EUR
(defvar *reas*) ;; TODO - only used in h24, never declared in EUR

;; Big group of related ones
(defvar *c-slot*) ;; also 'c-slot in applics?
(defvar *c-slot-sibs*)
(defvar *g-slot*)
(defvar *c-task*)
(defvar *c-from*)
(defvar *c-to*)

;; TODO - new ones, doublecheck their usage
(defvar *added-some*)
(defvar *involved-units*)


;; TODO - some of the higher numbered heuristics were out of lexical order in EUR, does that indicate anything about the age of the various units/heuristics in there? would it matter? I guess if some things are suspected incomplete, it could be useful to 


;; TODO - lambdas are stored as expression lists, they really should be compiled at compile-time. Maybe the macro could look for FAST-DEFN keys and check for a function name or lambda there. I don't think I've seen lisp code in any other property. UNITIZED-DEFN as well, FAST-ALG, RECURSIVE-ALG

(defmacro defheuristic (&rest rest)
  `(putprops ,@rest))


(defheuristic h1
  isa (heuristic op anything)
  english ("IF an op F (e.g., a mathematical function, a heuristic, etc.) has had some good applications, but over 4/5 are bad, THEN conjecture that some Specializations of F may be superior to F, and add tasks to specialize F to the Agenda.")
  if-potentially-relevant (lambda (f)
                            ;; ORIG: Check that F has some recorded applications -- which implies, of course, that F is an executable/performable entity
                            (applics f))
  if-truly-relevant (lambda (f)
                      ;; ORIG: Check that some Applics of F have high Worth, but most have low Worth
                      ;; ORIG: The extent to which those conditions are met will determine the amount of energy to expend working on applying this rule -- its overall relevancy
                      (and (some (lambda (a)
                                   ;; ORIG: these will have the format (args results)
                                   (some #'has-high-worth (cadr a)))
                                 (applics f))
                           (> 0.2 (setf *fraction* (fraction-of (map-union (applics f) #'cadr)
                                                                #'has-high-worth)))
                           (not (subsumed-by f))))
  worth 724
  applics (((sit1) (win1 los1))
           ((sit2) (los2 los3 los4 los5 los6))
           ((task-num 244) (h19-criterial) 3)
           ((task-num 23) (h5-criterial) 3)
           ((task-num 23) (h5-good) 3))
  abbrev ("Specialize a sometimes-useful action")
  then-print-to-user (lambda (f)
                       (cprin1 13 "~%" *conjec* ":~%Since some specializations of " f
                               " (i.e., " (abbrev f) ") are quite valuable, but over four-fifts are trash,"
                               " EURISKO has recognized the value of finding new concepts similar to -- "
                               "but more specialized than -- " f
                               ", and (to that end) has added a new task to the agenda to find such specializations. ")
                       t)
  then-conjecture (lambda (f)
                    (let ((*conjec* (new-name 'conjec)))
                      (create-unit *conjec* 'proto-conjec)
                      (put *conjec* 'english `("Specializations of" ,f "may be more useful than it is, since it has some good instances but many more poor ones. (" ,(percentify (- 1.0 *fraction*)) "are losers)"))
                      (put *conjec* 'abbrev `(,f "sometimes wins, usually loses, so specializations of it may win big"))
                      (put *conjec* 'worth (floor (average (nearness-to *fraction* 0.1)
                                                           (average-worths 'h1 f))))
                      (push *conjec* *conjectures*)))
  then-add-to-agenda (lambda (f)
                       (add-to-agenda (list (list (average-worths f 'h1)
                                                  f
                                                  'specializations
                                                  (list *conjec*)
                                                  (list (list 'credit-to 'h1)))))
                       (add-prop-l *task-results* 'new-tasks "1 unit must be specialized"))
  then-conjecture-record (2393 . 5)
  then-add-to-agenda-record (377 . 5)
  then-print-to-user-record (2601 . 5)
  overall-record (7078 . 5)
  arity 1)

(defheuristic h2
  isa (heuristic op anything)
  english "IF you have just finished a task, and some units were created, and one of the creators has the property of spewing garbage, THEN stuff that spewer"
  if-potentially-relevant NULL ;; TODO - never relevant? has this heuristic been disabled? is this the equivalent of NIL? it probably always returns NIL because the parameter is always a non-nil Unit? or is this actually passed NIL in some circumstances where this should fire?

  worth 700
  abbrev "Kill a concept that leads to lots of garbage"
  if-finished-working-on-task (lambda (task)
                                (declare (ignore task))
                                (and
                                 (assoc 'new-units *task-results*)
                                 (setf *pos-cred* (subset (self-intersect (map-union (cdr (assoc 'new-units *task-results*))
                                                                                     #'creditors))
                                                          (lambda (c)
                                                            ;; ORIG: See if C has generated many concepts none of which have any decent applics
                                                            (and
                                                             (memb c *new-u*)
                                                             (>= (length (applics c)) 10)
                                                             (every (lambda (z)
                                                                      (and (consp (cadr z))
                                                                           (every (lambda (a)
                                                                                    (null (applics a)))
                                                                                  (cadr z))))
                                                                    (applics c))))))))
  then-print-to-user (lambda (task)
                       (declare (ignore task))
                       (cprin1 14 "~%~%" (length *pos-cred*)
                               " units were reduced in Worth, due to excessive generation of mediocre concepts by them; namely: " *pos-cred* "~%")
                       (when *deleted-units*
                         (cprin1 14 "~%~%" (length *deleted-units*)
                                 " had Worths that were now so low, the whole concept was obliterated;"
                                 " namely; " *deleted-units* "~%~%"))
                       (setf *pos-cred* nil)
                       (setf *deleted-units* nil)
                       t)
  then-compute (lambda (task)
                 (declare (ignore task))
                 (and (boundp '*pos-cred*)
                      (consp *pos-cred*)
                      (or (mapc #'punish-severely *pos-cred*)
                          t)
                      (add-task-results
                       'punished-units
                       `(,*pos-cred* "because they've led to so many questionable units being created!"))))
  then-delete-old-concepts (lambda (task)
                             (declare (ignore task))
                             (setf *deleted-units* nil)
                             (mapc (lambda (c)
                                     (when (<= (worth c) 175)
                                       (push c *deleted-units*)
                                       (mapc (lambda (r)
                                               (apply-rule r c ", before we delete it."))
                                             (examples 'hind-sight-rule))
                                       (kill-unit c)))
                                   *pos-cred*)
                             (when *deleted-units*
                               (add-task-results 'deleted-units
                                                 `(,*deleted-units* "because their Worth has fallen so low")))
                             t)
  arity 1)

(defheuristic h3
  isa (heuristic op anything)
  english "IF the current task is to specialize a unit, but no specific slot to specialize is yet known, THEN choose one"
  if-potentially-relevant null
  worth 101
  applics (((sit1) (win1 los1)))
  abbrev "Randomly choose a slot to specialize"
  if-working-on-task (lambda (task)
                       (declare (ignore task))
                       (and (is-a-kind-of *cur-slot* 'specializations)
                            (null (assoc 'slot-to-change *cur-sup*))
                            (>= 11 (the-number-of (lambda (z)
                                                    (and (eq *cur-unit* (extract-unit-name z))
                                                         (eq *cur-slot* (extract-slot-name z))))
                                                  *agenda*))))
  then-print-to-user (lambda (task)
                       (declare (ignore task))
                       (cprin1 13 "~%" *new-reason* "~%~%")
                       t)
  then-add-to-agenda (lambda (task)
                       (declare (ignore task))
                       (add-to-agenda (list (list (average *cur-pri* (average-worths *cur-unit* 'h3))
                                                  *cur-unit* *cur-slot*
                                                  (cons (setf *new-reason*
                                                              (list "A new unit will be created by specializing the"
                                                                    *slot-to-change* "slot of" *cur-unit* "; that slotw as chosen randomly."))
                                                        nil)
                                                  (list (list 'slot-to-change *slot-to-change*)
                                                        (list 'credit-to 'h3 *credit-to*)))))
                       (add-task-results 'new-tasks
                                         `("1 specific slot of" *cur-unit* "to find" *cur-slot* "of")))
  then-compute (lambda (task)
                 (declare (ignore task))
                 (setf *slot-to-change* (random-choose (set-intersect (slot-names *cur-unit*)
                                                                      (examples 'slot))))
                 (setf *credit-to* (cdr (assoc 'credit-to *cur-sup*)))
                 t)
  subsumed-by (h5 h5-criterial h5-good)
  arity 1)

(defheuristic h4
  isa (heuristic op anything)
  english "IF a new unit has been synthesized, THEN place a task on the Agenda to gather new empirical data about it"
  if-potentially-relevant null
  worth 703
  applics (((sit1)
            (win1 los1)))
  abbrev (about concepts gather data new empirical)
  if-finished-working-on-task (lambda (task)
                                (declare (ignore task))
                                (setf *new-units* (subset (cdr (assoc 'new-units *task-results*))
                                                          #'unitp)))
  then-print-to-user (lambda (task)
                       (declare (ignore task))
                       (cprin1 13 "~%" (length *new-units*) " new units ")
                       (cprin1 33 ", namely " *new-units* ", ")
                       (cprin1 13 "were defined.  New tasks are being added to the agenda to ensure that empirical data about them will soon be gathered.~%~%")
                       t)
  then-add-to-agenda (lambda (task)
                       (declare (ignore task))
                       (add-to-agenda (mapcar (lambda (new-unit)
                                                (list (average-worths new-unit 'h4)
                                                      new-unit
                                                      (instances new-unit)
                                                      '("After a unit is synthesized, it is useful to seek instances of it.")
                                                      '((credit-to h4))))
                                              *new-units*))
                       (setf *task-results* (add-task-results 'new-tasks (cons (length *new-units*)
                                                                               '(new units must have instances found)))))
  then-add-to-agenda-record (30653 . 87)
  then-print-to-user-record (18543 . 87)
  overall-record (68827 . 72)
  arity 1)

(defheuristic h5
  isa (heuristic op anything)
  english "IF the current task is to specialize a unit, and no specific slot has been chosen to be the one changed, THEN randomly select which slots to specialize"
  if-potentially-relevant null
  worth 151
  applics (((sit1)
            (win1 los1))
           ((task-num 244)
            (h19-criterial)
            2)
           ((task-num 23)
            (h5-criterial)
            2)
           ((task-num 23)
            (h5-good)
            2))
  abbrev "Choose some particular slots of u to specialize"
  if-working-on-task (lambda (task)
                       (declare (ignore task))
                       (and (is-a-kind-of *cur-slot* 'specializations)
                            (null (assoc 'slot-to-change *cur-sup*))
                            (>= 7 (the-number-of *agenda* (lambda (z)
                                                            (and (eq *cur-unit* (extract-unit-name z))
                                                                 (eq *cur-slot* (extract-slot-name z))))))))
  then-print-to-user (lambda (task)
                       (declare (ignore task))
                       (cprin1 13 "~%" *cur-unit* " will be specialized by specializing the following of its slots: "
                               *slots-to-change* "~%~%")
                       t)
  then-add-to-agenda (lambda (task)
                       (declare (ignore task))
                       (add-to-agenda (sort (mapcar (lambda (s)
                                                      (list (average *cur-pri* (average-worths s 'h5))
                                                            *cur-unit*
                                                            *cur-slot*
                                                            (list (setf *new-reason*
                                                                        (list "A new unit will be created by specializing the "
                                                                              s " slot of " *cur-unit*
                                                                              "; that slot was chosen randomly.")))
                                                            (list (list 'slot-to-change s)
                                                                  (cons 'credit-to (cons 'h5 *credit-to*)))))
                                                    *slots-to-change*)
                                            #'order-tasks))
                       (add-task-results 'new-tasks (list (length *slots-to-change*)
                                                          " specific slots of " *cur-unit* " to find " *cur-slot* " of")))
  then-compute (lambda (task)
                 (declare (ignore task))
                 (setf *slots-to-change* (random-subset (set-intersect (slot-names *cur-unit*)
                                                                       (examples 'slot))))
                 (setf *credit-to* (cdr (assoc 'credit-to *cur-sup*)))
                 t)
  subsumes (h3)
  subsumed-by (h5-criterial h5-good)
  arity 1)

;; TODO - I bet raw H5 was written before the notion of criterial slots was established
(defheuristic h5-criterial
  isa (heuristic op anything)
  english "IF the current task is to specialize a unit, and no specific slot has been chosen to be the one changed, THEN randomly select which criterial slots to specialize."
  if-potentially-relevant null
  worth 700
  abbrev "Choose some particular criterial slots of u to specialize"
  if-working-on-task (lambda (task)
                       (declare (ignore task))
                       (and (is-a-kind-of *cur-slot* 'specializations)
                            (null (assoc 'slot-to-change *cur-sup*))
                            (>= 7 (the-number-of *agenda* (lambda (z)
                                                            (and (eq *cur-unit* (extract-unit-name z))
                                                                 (eq *cur-slot* (extract-slot-name z))))))))
  then-print-to-user (lambda (task)
                       (declare (ignore task))
                       (cprin1 13 "~%" *cur-unit* " will be specialized by specializing the following of its criterial slots: "
                               *slots-to-change* "~%~%")
                       t)
  then-add-to-agenda (lambda (task)
                       (declare (ignore task))
                       (add-to-agenda (sort (mapcar (lambda (s)
                                                      (list (average *cur-pri* (average-worths s 'h5-criterial))
                                                            *cur-unit*
                                                            *cur-slot*
                                                            (cons (setf *new-reason*
                                                                        (list "A new unit will be created by specializing the "
                                                                              s "slot of " *cur-unit*
                                                                              "; that criterial slot was chosen randomly."))
                                                                  nil)
                                                            (list (list 'slot-to-change s)
                                                                  (cons 'credit-to
                                                                        (cons 'h5-criterial
                                                                              *credit-to*)))))
                                                    *slots-to-change*)
                                            #'order-tasks))
                       (add-task-results 'new-tasks
                                         (list (length *slots-to-change*)
                                               (list "Specific criterial slots of " *cur-unit* " to find " *cur-slot* " of"))))
  then-compute (lambda (task)
                 (declare (ignore task))
                 (setf *slots-to-change* (random-subset (set-intersect (slot-names *cur-unit*)
                                                                       (examples 'criterial-slot))))
                 (setf *credit-to* (cdr (assoc 'credit-to *cur-sup*)))
                 t)
  subsumes (h3 h5)
  creditors (h6 h5 h1)
  then-compute-record (3850 . 46)
  then-add-to-agenda-record (12150 . 46)
  then-print-to-user-record (7532 . 46)
  overall-record (37450 . 46)
  arity 1)

(defheuristic h5-good
  isa (heuristic op anything)
  english "IF the current task is to specialize a unit, and no specific slot has been chosen to be the one changed, THEN choose a good set of sllots to specialize"
  if-potentially-relevant null
  worth 700
  abbrev "Choose some particular good slots of u to specialize"
  if-working-on-task (lambda (task)
                       (declare (ignore task))
                       (and (is-a-kind-of *cur-slot* 'specializations)
                            (null (assoc 'slot-to-change *cur-sup*))
                            (>= 7 (the-number-of *agenda* (lambda (z)
                                                            (and (eq *cur-unit* (extract-unit-name z))
                                                                 (eq *cur-slot* (extract-slot-name z))))))))
  then-print-to-user (lambda (task)
                       (declare (ignore task))
                       (cprin1 13 "~%" *cur-unit* " will be specialized by specializing the following of its good slots: "
                               *slots-to-change* "~%~%")
                       t)
  then-add-to-agenda (lambda (task)
                       (declare (ignore task))
                       (add-to-agenda (sort (mapcar (lambda (s)
                                                      (list (average *cur-pri* (average-worths s 'h5-good))
                                                            *cur-unit*
                                                            *cur-slot*
                                                            (list (setf *new-reason*
                                                                        (list "A new unit will be created by specializing the "
                                                                              s " slot of " *cur-unit*
                                                                              "; that slot was chosen because of its high worth.")))
                                                            (list (list 'slot-to-change s)
                                                                  (cons 'credit-to (cons 'h5-good *credit-to*)))))
                                                    *slots-to-change*)
                                            #'order-tasks))
                       (add-task-results 'new-tasks (list (length *slots-to-change*)
                                                          " specific good slots of " *cur-unit*
                                                          " to find " *cur-slot* " of")))
  then-compute (lambda (task)
                 (declare (ignore task))
                 (setf *slots-to-change* (good-subset (set-intersect (slot-names *cur-unit*)
                                                                     (examples 'slot))))
                 (setf *credit-to* (cdr (assoc 'credit-to *cur-sup*)))
                 t)
  subsumes (h3 h5)
  creditors (h6 h5 h1)
  then-compute-record (10632 . 46)
  then-add-to-agenda-record (23977 . 46)
  then-print-to-user-record (8399 . 46)
  overall-record (56898 . 46)
  arity 1)

(defheuristic h6
  isa (heuristic op anything)
  english "IF the current task is to specialize a unit, and a slot has been chosen to be the one changed, THEN randomly select a part of it and specialize that part"
  if-potentially-relevant null
  worth 700
  abbrev "Specialize a given slot of a given unit"
  if-working-on-task (lambda (task)
                       (declare (ignore task))
                       (and (is-a-kind-of *cur-slot* 'specializations)
                            (setf *slot-to-change* (cadr (assoc 'slot-to-change *cur-sup*)))))
  then-print-to-user (lambda (task)
                       (declare (ignore task))
                       (cprin1 13 "~%Specialized the " *slot-to-change* " slot of " *cur-unit*
                               ", replacing its old value ")
                       (cprin1 48 "(which was " *old-value* ") ")
                       (cprin1 14 "by " *new-value* ".~%")
                       (cprin1 13 "~%")
                       t)
  then-compute (lambda (task)
                 (declare (ignore task))
                 ;; ORIG: assumes the existence of funcctions SpecializeLispPred,
                 ;;  SpecializeLispFn, SpecializeList, and of course SpecializeNIL to catch
                 ;;  the slots which have not DataType slot
                 ;; TODO - does he mean to catch the units instead?
                 (setf *u-diff* nil)
                 (setf *are-units* nil)
                 (setf *have-spec* nil)
                 ;; TODO - grok this. it's passing the old value of the slot, and the new value is returned?
                 (setf *new-value* (funcall (pack* 'specialize (data-type *slot-to-change*))
                                            (setf *old-value* (funcall *slot-to-change* *cur-unit*))))
                 ;; TODO - have-spec was just set NIL, but some of the prev line's functions might have mutated it?
                 (let ((need-spec (set-diff *are-units* *have-spec*)))
                   ;; ORIG: If the OldValue and NewValue are equal, then we really haven't
                   ;;  specialized it at all, so we want to return NIL and have this rule FAIL
                   (mapc #'tiny-reward *have-spec*)
                   (when *have-spec*
                     (add-task-results 'rewarded-units
                                       ;; TODO - clean up this list construct
                                       (cons *have-spec*
                                             (append '("because they coud have been used in specializing")
                                                     (list *cur-unit*)))))
                   (add-to-agenda (mapcar (lambda (ns)
                                            (list (half *cur-pri*)
                                                  ns
                                                  'specializations
                                                  `((,*cur-unit*
                                                     " might have been specialized better, earlier, if some specializations had existed for"
                                                     ,@ns))
                                                  '((credit-to h6))))
                                          need-spec))
                   (when need-spec
                     (add-task-results 'new-tasks
                                       `(,need-spec
                                         " will be specialized, because if such specializations had existed, we could have used them just now while trying to specialize"
                                         *cur-unit*))))
                 (cond ((equal *old-value* *new-value*)
                        (cprin1 15 "~%Hmmm... couldn't seem to find any meaningful specialization of the "
                                *slot-to-change* " slot of " *cur-unit* "~%")
                        nil)
                       ((> *verbosity* 15)
                        (cprin1 15 "~%Inside the " *slot-to-change* " slot, ")
                        (maprint *u-diff*)
                        (terpri)
                        t)
                       (t t)))
  then-define-new-concepts (lambda (task)
                             (let ((new-unit (create-unit *cur-unit* *cur-unit*)))
                               (dolist (s (sib-slots *slot-to-change*))
                                 (kill-slot new-unit s))
                               (put new-unit *slot-to-change* *new-value*)
                               (setf *new-units* (cdr (assoc 'new-units *task-results*)))
                               (if *new-units*
                                   (nconc1 new-unit *new-units*)
                                   (push (list 'new-units new-unit) *task-results*))
                               (addprop 'h6 'applics
                                        (list (list 'task-num *task-num* task (date))
                                              (list new-unit)
                                              (initialize-credit-assignment)
                                              (list "Specialized " *slot-to-change* "slot of"
                                                    *cur-unit* "as follows:" *u-diff*)))
                               (dolist (h (setf *creditors* (cdr (assoc 'credit-to *cur-sup*))))
                                 (addprop h 'applics
                                          (list (list 'task-num *task-num*)
                                                (list new-unit)
                                                (decrement-credit-assignment))))
                               (put new-unit 'creditors (push 'h6 *creditors*))
                               (addprop *cur-unit* 'specializations new-unit)
                               (addprop new-unit 'generalizations *cur-unit*))
                             t)
  applics (((task-num 244 (h19 specializations ((slot-to-change if-finished-working-on-task)))
                      "29-Mar-81 16:28:41")
            (h19-criterial)
            1
            ("Specialized" if-finished-working-on-task "slot of" h19 "as follows:" (slot -> criterial-slot)))
           ((task-num 23 (h5 specializations ((slot-to-change then-compute)))
                      "29-Mar-81 16:28:41")
            (h5-criterial)
            1
            ("Specialized" then-compute "slot of" h5 "as follows:" (slot -> criterial-slot)))
           ((task-num 23 (h5 specializations ((slot-to-change then-compute)))
                      "29-Mar-81 16:28:55")
            (h5-good)
            1
            ("Specialized" then-compute "slot of" h5 "as follows:" (random-subset -> good-subset))))
  then-compute-record (58183 . 73)
  then-define-new-concepts-record (74674 . 73)
  then-print-to-user-record (31470 . 73)
  overall-record (188387 . 73)
  then-compute-failed-record (24908 . 56)
  arity 1)

(defheuristic h7
  isa (heuristic op anything)
  english "IF a concept has no known instances, THEN try to find some"
  if-potentially-relevant (lambda (f)
                            ;; ORIG: check that f has some recorded applications -- which
                            ;;       implies, of course, that f is an executable/performable entity
                            (null (funcall (instances f) f)))
  if-truly-relevant (lambda (f)
                      ;; TODO - two ISA calls that can be cached?
                      (or (memb 'category (isa f))
                          (memb 'op (isa f))))
  worth 700
  abbrev ("Instantiate a concept having no known instances")
  then-print-to-user (lambda (f)
                       (cprin1 13 "~%Since " f " has no known " (instances f)
                               ", it is probably worth looking for some.~%")
                       t)
  then-add-to-agenda (lambda (f)
                       (add-to-agenda `((,(average-worths f 'h7)
                                         ,f
                                         ,(instances f)
                                         (,(subst f 'f '("To properly study " f " we must gather empirical data about instances of that concept")))
                                         ((credit-to h7)))))
                       (add-task-results 'new-tasks '("1 unit must be instantiated")))
  then-add-to-agenda-record (11017 . 172)
  then-print-to-user-record (21543 . 172)
  overall-record (71147 . 172)
  arity 1)

(defheuristic h8
  isa (heuristic op anything)
  english "IF the current task is to find application-instances of a unit, and it has a algorithm, THEN look over instances of generalizations of the unit, and see if any of them are valid application-instances of this as well"
  if-potentially-relevant null
  worth 700
  ;; TODO - are the sublists in here evaluated?
  abbrev (Applics (u) may be found against Applics (genl (u)))
  if-working-on-task (lambda (task)
                       (declare (ignore task))
                       (and (eq *cur-slot* 'applics)
                            (setf *alg-to-use* (alg *cur-unit*))
                            (setf *space-to-use* (subset (set-diff (subset (or (generalizations *cur-unit*)
                                                                               (self-intersect (mapappend (isa *cur-unit*)
                                                                                                          'examples)))
                                                                           'applics)
                                                                   (cons *cur-unit* (specializations *cur-unit*)))
                                                         (lambda (f)
                                                           (eq (arity f)
                                                               (arity *cur-unit*)))))))
  then-print-to-user (lambda (task)
                       (declare (ignore task))
                       (cprin1 13 "~%Instantiated " *cur-unit* "; found "
                               (length *new-values*) " " 'applics "~%")
                       (cprin1 48 "     Namely: " *new-values* "~%")
                       t)
  ;; TODO - the lambda had a 2nd parameter *domain-tests*, but unless map-applics actually ran the other uses, this doesn't make sense for dynamic scope.
  then-compute (lambda (task) ;; *domain-tests*
                 (declare (ignore task))
                 ;; Commented-out source code
                 ;; ORIG: [* (PUTD (QUOTE APPLYTOUSE)
                 ;;                (GETD (COND ((AND (Arity CurUnit)
                 ;;                                  (IGREATERP (Arity CurUnit) 1))
                 ;;                             (QUOTE APPLY))
                 ;;                            (T (QUOTE APPLY*]
                 (setf *cur-val* (funcall *cur-slot* *cur-unit*))
                 (setf *domain-tests* (mapcar #'defn (domain *cur-unit*)))
                 (dolist (z *space-to-use*)
                   (map-applics z (lambda (i)
                                    (and (not (known-applic *cur-unit* (applic-args i)))
                                         (equal (length *domain-tests*)
                                                (applic-args i))
                                         ;; TODO - verify translation of "(for DT in DomainTests as A in (ApplicArgs I) ..."
                                         ;; TODO - could be a 2-list mapc as well
                                         (loop for dt in *domain-tests*
                                               for a in (applic-args i)
                                               always (funcall dt a))
                                         ;; TODO - orig (errorset '(apply *alg-to-use* (applic-args i)) 'nobreak)
                                         ;;  The 'nobreak portion disables breaks for timeout or something? not sure
                                         (let ((temp (ignore-errors (apply *alg-to-use* (applic-args i)))))
                                           (union-prop *cur-unit* 'applics (list (applic-args i) (car temp))))))
                                100))
                 (and (setf *new-values* (set-difference (applics *cur-unit*)
                                                         *cur-val*))
                      ;; TODO - does the differing value between PUSH and (setf *task-results* (cons ...)) make a difference here?
                      ;; pattern occurs multiple places
                      (push (list 'new-values
                                  (list *cur-unit* *cur-slot* *new-values*
                                        (list "By examining Applics of" *space-to-use*
                                              ", Eurisko found" *new-values*
                                              "of them wre also applics of" *cur-unit*)))
                            *task-results*)))
  then-compute-failed-record (635979 . 66)
  then-compute-record (368382 . 10)
  then-print-to-user-record (3893 . 10)
  overall-record (375388 . 10)
  arity 1)

(defheuristic h9
  isa (heuristic op anything)
  english "IF the current task is to find examples of a unit, and it has a definition, THEN look over instances of generalizations of the unit, and see if any of them are valid examples of this as well"
  if-potentially-relevant null
  worth 700
  abbrev "Ecx (u) may be found amongst Exs (genl (u))"
  if-working-on-task (lambda (task)
                       (declare (ignore task))
                       (and (eq *cur-slot* 'examples)
                            (setf *defn-to-use* (defn *cur-unit*))
                            (setf *space-to-use* (set-diff (or (generalizations *cur-unit*)
                                                               (self-intersect (mapappend (isa *cur-unit*) 'examples)))
                                                           (cons *cur-unit* (specializations *cur-unit*))))))
  then-print-to-user (lambda (task)
                       (declare (ignore task))
                       (cprin1 13 "~%Instantiated " *cur-unit* "; found "
                               (length *new-values*) " " 'examples "~%")
                       (cprin1 48 "     Namely: " *new-values* "~%")
                       t)
  then-compute (lambda (task)
                 (declare (ignore task))
                 (setf *cur-val* (funcall *cur-slot* *cur-unit*))
                 (let ((*user-impatience* (max 1 (floor *user-impatience*
                                                        (max 1 (length *space-to-use*))))))
                   (dolist (z *space-to-use*)
                     (map-examples z (lambda (i)
                                       ;; ORIG: If the proposed example is already on Examples,
                                       ;;       or already on NonExamples, then we can stop immediately
                                       (and (not (member i (examples *cur-unit*)))
                                            (not (member i (non-examples *cur-unit*)))
                                            (cond
                                              ((funcall *defn-to-use* i)
                                               (cprin1 57 "+")
                                               t)
                                              (t (cprin1 59 "-")
                                                 nil))
                                            (union-prop *cur-unit* 'examples i)))
                                   400)
                     (and (setf *new-values* (set-difference (examples *cur-unit*) *cur-val*))
                          (push (list 'new-values (list *cur-unit* *cur-slot* *new-values*
                                                        (list "By examining examples of" *space-to-use*
                                                              ", Eurisko found" *new-values*
                                                              "of them were also Examples of" *cur-unit*)))
                                *task-results*)))))
  then-compute-record (533544 . 7)
  then-print-to-user-record (5014 . 7)
  overall-record (541853 . 7)
  then-compute-failed-record (912711 . 5)
  arity 1)

(defheuristic h10
  isa (heuristic op anything)
  english "IF the current task is to find examples of a unit, and it is the range of some operation f, THEN gather together the outputs of the I/O pairs stored on Applics of f"
  if-potentially-relevant null
  worth 700
  abbrev "If C is Range (f), then Exs (C) can be gotten from Applics (f)"
  if-working-on-task (lambda (task)
                       (declare (ignore task))
                       (and (eq *cur-slot* 'examples)
                            (setf *op-to-use* (random-choose (is-range-of *cur-unit*)))))
  then-print-to-user (lambda (task)
                       (declare (ignore task))
                       (cprin1 13 "~%Instantiated " *cur-unit* "; there are now "
                               (length (examples *cur-unit*)) " " 'examples "~%")
                       (cprin1 48 "    The new ones are: " *new-values* "~%")
                       t)
  then-compute (lambda (task)
                 (declare (ignore task))
                 (setf *cur-val* (funcall *cur-slot* *cur-unit*))
                 (when (setf *space-to-use* (applics *op-to-use*))
                   (dolist (z *space-to-use*)
                     (setf z (extract-output z))
                     (and (not (member z (examples *cur-unit*)))
                          (not (member z (non-examples *cur-unit*)))
                          (cprin1 58 "+")
                          (union-prop *cur-unit* 'examples z))))
                 (when (setf *new-values* (set-difference (examples *cur-unit*) *cur-val*))
                   (add-task-results 'new-values
                                     `(,*cur-unit*
                                      ,*cur-slot*
                                      ,*new-values*
                                      '("By examining Applics of" ,*op-to-use*
                                        ", Eurisko found" ,*new-values* 'examples "of" ,*cur-unit*))))
                 ;; ORIG: this always returns T ; if the SpaceToUse was null, then
                 ;;       ThenAddToAgenda will want to add a task to the agenda to help correct that situation
                 t)
  then-add-to-agenda (lambda (task)
                       (declare (ignore task))
                       (cond (*space-to-use* ;; ORIG: There were some Applics of OpToUse
                              t)
                             (t (add-to-agenda `((,(1- *cur-pri*) ,*op-to-use* applics
                                                  (("Recent task was stymied for lack of such applics; namely trying to find Examples of"
                                                    ,*cur-unit*))
                                                  ((credit-to h10)))
                                                 (,(floor *cur-pri* 2) ,*cur-unit* ,*cur-slot*
                                                  (("Had to suspend whilst gathering Applics of" ,*op-to-use*)
                                                   ,(car *cur-reasons*))
                                                  ,*cur-sup*)))
                                (add-task-results 'new-tasks
                                                  `("1 task to find Applics of"
                                                    ,*op-to-use*
                                                    "and 1 task just like the current one"))
                                (cprin1 40 "~%Hmmm... can't proceed with this until some Applics of " *op-to-use* " are known.~%")
                                nil)))
  then-compute-record (12618 . 7)
  then-add-to-agenda-failed-record (1307 . 3)
  then-add-to-agenda-record (37 . 4)
  then-print-to-user-record (2101 . 4)
  overall-record (16037 . 4)
  arity 1)

(defheuristic h11
  isa (heuristic op anything)
  english "IF the current task is to find application-instances of a unit f, and it has an Algorithm for computing its values, and it has a Domain, THEN choose examples of its domain component/s, and run the alg for f on such inputs"
  if-potentially-relevant null
  worth 700
  abbrev "Applics (f) may be found by running Alg (f) on members of u's Domain)"
  if-working-on-task (lambda (task)
                       (declare (ignore task))
                       (and (eq *cur-slot* 'applics)
                            (setf *alg-to-use* (alg *cur-unit*))
                            (setf *space-to-use* (domain *cur-unit*))))
  then-print-to-user (lambda (task)
                       (declare (ignore task))
                       (cprin1 13 "~%Instantiated " *cur-unit* "; found "
                               (length *new-values*) " " 'applics "~%")
                       (cprin1 48 "    Namely: " *new-values* "~%")
                       t)
  then-compute (lambda (task)
                 (declare (ignore task))
                 (let ((args nil)
                       (failed nil)
                       (n-tried nil))
                   ;; ORIG: (PUTD (QUOTE APPLYTOUSE)
                   ;;             (GETD (COND ((AND (Arity CurUnit)
                   ;;                               (IGREATERP (Arity CurUnit)
                   ;;                               1))
                   ;;                          (QUOTE APPLY))
                   ;;                         (T (QUOTE APPLY*)))))
                   (setf *cur-val* (funcall *cur-slot* *cur-unit*))
                   (setf *domain-tests* (mapcar #'defn (domain *cur-unit*)))
                   (setf *max-rule-time* (+ (clock 0)
                                            (* *cur-pri* *user-impatience* 5
                                               (1+ (floor (+ 0.5 (log (max 2 (1+ *verbosity*)))))))))
                   (setf *max-rule-space* (* 2 (+ (average *cur-pri* 1000)
                                                  (count (getprop *cur-unit* *cur-slot*)))))
                   ;; TODO - only usage of this var ever, even in EUR
                   (setf *rule-cycle-time* (clock 0))
                   (case (length *domain-tests*)
                     (0 (loop for j from 1 upto 100
                              do (and (not (known-applic *cur-unit* nil))
                                      (cprin1 62 "+")
                                      (union-prop *cur-unit* 'applics
                                                  `(nil ,(funcall *alg-to-use* nil))))
                              until (rule-taking-too-long)
                              finally (setf n-tried j)))
                     (1 (cond ((generator (car (domain *cur-unit*)))
                               (setf n-tried 0)
                               (map-examples (car (domain *cur-unit*))
                                             (lambda (a)
                                               (and (not (known-applic *cur-unit* (list a)))
                                                    (funcall (car *domain-tests*) a)
                                                    (cprin1 61 "+")
                                                    (incf n-tried)
                                                    (union-prop *cur-unit* 'applics
                                                                `((,a)
                                                                  ,(funcall *alg-to-use* a)))))
                                             200))
                              (t (loop for j from 1 upto 50
                                       do (and (setf args (mapcar (lambda (d)
                                                                    (let ((tmp nil))
                                                                      (cond ((generator d)
                                                                             (let ((lastgen nil))
                                                                               (map-examples d (lambda (e)
                                                                                                 (setf lastgen e))
                                                                                             (rand 1 100))
                                                                               (return lastgen)))
                                                                            ((examples d)
                                                                             (random-choose (examples d)))
                                                                            ((setf tmp (examples (random-choose (specializations d))))
                                                                             (random-choose tmp))
                                                                            ((put d 'examples (gather-examples d))
                                                                             (setf *temp-caches* `((remprop ',d 'examples)))
                                                                             (random-choose (examples d)))
                                                                            (t (setf failed t)
                                                                               nil))))
                                                                  *space-to-use*))
                                               (not failed)
                                               (not (known-applic *cur-unit* args))
                                               ;; TODO - repeated test
                                               (loop for dt in *domain-tests*
                                                     for a in args
                                                     always (funcall dt a))
                                               (let ((maybe-failed nil))
                                                 (union-prop *cur-unit* 'applics
                                                             (list args
                                                                   ;; TODO - was (ERRORSET .. 'NOBREAK)
                                                                   (car (setf maybe-failed (ignore-errors
                                                                                            (apply *alg-to-use* args)))))
                                                             nil
                                                             (setf maybe-failed (or (null maybe-failed)
                                                                                    (eq (car maybe-failed)
                                                                                        'failed))))
                                                 (cprin1 62 (if maybe-failed "-" "+"))))
                                       until (rule-taking-too-long)
                                       finally (setf n-tried j)))))
                     (otherwise (loop for j from 1 upto 50
                                      do (and (setf args (mapcar (lambda (d)
                                                                   (let ((tmp nil))
                                                                     (cond ((generator d)
                                                                            (let ((lastgen nil))
                                                                              (map-examples d (lambda (e)
                                                                                                (setf lastgen e))
                                                                                            (rand 1 50))
                                                                              (return lastgen)))
                                                                           ((examples d)
                                                                            (random-choose (examples d)))
                                                                           ((setf tmp (examples (random-choose (specializations d))))
                                                                            (random-choose tmp))
                                                                           ((put d 'examples (gather-examples d))
                                                                            (setf *temp-caches* `(remprop ',d 'examples))
                                                                            (random-choose (examples d)))
                                                                           (t (setf failed t)
                                                                              nil))))
                                                                 *space-to-use*))
                                              (not failed)
                                              (not (known-applic *cur-unit* args))
                                              (loop for dt in *domain-tests*
                                                    for a in args
                                                    always (funcall dt a))
                                              (let ((maybe-failed nil))
                                                (union-prop *cur-unit* 'applics
                                                            (list args
                                                                  ;; TODO - was (ERRORSET .. 'NOBREAK)
                                                                  (car (setf maybe-failed (ignore-errors
                                                                                           (apply *alg-to-use* args)))))
                                                            nil
                                                            (setf maybe-failed (or (null maybe-failed)
                                                                                   (eq (car maybe-failed)
                                                                                       'failed))))
                                                (cprin1 62 (if maybe-failed "-" "+"))))
                                      until (rule-taking-too-long)
                                      finally (setf n-tried j))))
                   (and (setf *new-values* (set-difference (applics *cur-unit*) *cur-val*))
                                        ;: TODO - some of the add-task-results should be a simple push, not adding key/val stuff!
                        (push (list 'new-values
                                    (list *cur-unit* *cur-slot* *new-values*
                                          (list "By running algorithm for" *cur-unit* "on random examples from"
                                                (domain *cur-unit*) "," (length *new-values*) "were found")))
                              *task-results*)
                        (setf *cur-val* (funcall *cur-slot* *cur-unit*))
                        (put *cur-unit* 'rarity
                             (let* ((rcu (rarity *cur-unit*))
                                    (nt (add-nn (length *new-values*)
                                                (cadr rcu)))
                                    (nf (add-nn (- n-tried (length *new-values*))
                                                (caddr rcu))))
                               (list (floor (float nt) (+ nt nf))
                                     nt nf))))))
  then-compute-record (2296694 . 66)
  then-print-to-user-record (47517 . 66)
  overall-record (2369179 . 66)
  then-compute-failed-record (1319487 . 23)
  arity 1)

(defheuristic h12
  isa (hind-sight-rule heuristic op anything)
  english "IF C is about to die, then try to form a new heuristic, one which -- had it existed earlier -- would have prevented C from ever being defined in the first place"
  if-potentially-relevant (lambda (f)
                            (memb f *deleted-units*))
  worth 700
  abbrev "Form a rule that would have prevented this mistake"
  then-print-to-user (lambda (task)
                       (declare (ignore task))
                       (cprin1 13 "~%~%Just before destroying a losing concept, Eurisko generalized from that bad experience, in the following way: "
                               "Eurisko will no longer alter the " *c-slot* " slot of a unit "
                               "when trying to find " *g-slot* " of that unit.  We learned our lesson from " *arg-unit* "~%~%"))
  then-compute (lambda (c)
                 (and (setf *c-slot* (cadr (assoc 'slot-to-change
                                                  (car (cddddr (setf *c-task* (caddar (find-if (lambda (a)
                                                                                                 (memb c (cadr a)))
                                                                                               (applics (car (creditors c)))))))))))
                      (setq *g-slot* (caddr *c-task*))
                      (or (<= (length (setf *c-slot-sibs* (sib-slots *c-slot*)))
                              50)
                          (setf *c-slot-sibs* (list *c-slot*)))
                      (or *c-slot-sibs* (setf *c-slot-sibs* (list *c-slot*)))))
  then-define-new-concepts (lambda (task)
                             (let ((new-unit (create-unit 'h-avoid 'h-avoid)))
                               (setproplist new-unit (subpair '(g-slot c-slot c-slot-sibs not-for-real)
                                                              (list *g-slot* *c-slot* *c-slot-sibs* t)
                                                              (getproplist new-unit)))
                               (setf *new-units* (cdr (assoc 'new-units *task-results*)))
                               (cond (*new-units* (nconc1 *new-units* new-unit))
                                     (t (push (list 'new-units new-unit) *task-results*)))
                               (addprop 'h12 'applics
                                        `((task-num ,*task-num* ,task ,(date))
                                          (,new-unit)
                                          ,(initialize-credit-assignment)
                                          ("Will avoid"
                                           ,*c-slot*
                                           ,@(cond ((cdr *c-slot-sibs*)
                                                    `(", actually all of these:" ,*c-slot-sibs* ","))
                                                   (t '(",")))
                                           "of units whenever finding" ,*g-slot* "of them")))
                               ;; TODO - oft repeated pattern, requires understanding of task format to name properly
                               (dolist (h (setf *creditors* (cdr (assoc 'credit-to *cur-sup*))))
                                 (lambda (h)
                                   (addprop h 'applics
                                            `((task-num ,*task-num* ,task ,(date))
                                              (,new-unit)
                                              ,(decrement-credit-assignment)))))
                               (put new-unit 'creditors (push 'h2 *creditors*)))
                             t)
  applics (((task-num 87 (h1-11 applics) "29-Mar-81 16:36:00")
            (h-avoid-if-working)
            1
            ("Specialized" h-avoid "as follows:" ((c-from -> and)
                                                  (c-to -> the-first-of)
                                                  (c-slot -> if-working-on-task)
                                                  (c-slot-sibs -> (if-potentially-relevant
                                                                   if-truly-relevant
                                                                   if-about-to-work-on-task
                                                                   if-working-on-task
                                                                   if-finished-working-on-task))
                                                  (g-slot -> generalizations)))))
  arity 1)

(defheuristic h13
  isa (hind-sight-rule heuristic op anything)
  english "IF C is about to die, then try to form a new heuristic, one which -- had it existed earlier -- would have prevented C from ever being defined in the first place, by preventing the kind of changed object from being changed"
  if-potentially-relevant (lambda (f)
                            (memb f *deleted-units*))
  worth 700
  abbrev "From a rule that would have prevented this mistake"
  then-print-to-user (lambda (task)
                       (declare (ignore task))
                       (cprin1 13 "~%~%Just before destroying a losing concept, Eurisko generalized from that bad experience in the following way: "
                               "Eurisko will no longer alter the " *c-from*
                               " inside any of these " *c-slot-sibs*
                               " slots of a unit when trying to find " *g-slot*
                               " of that unit.  We learned our lesson from " *arg-unit* "~%~%"))
  then-compute (lambda (c)
                 (let ((c-t-res (find-if (lambda (a)
                                           (memb c (cadr a)))
                                         (applics (car (creditors c))))))
                   (and (setf *c-slot* (cadr (assoc 'slot-to-change
                                                    (car (cddddr (setf *c-task* (caddar c-t-res)))))))
                        (setf *g-slot* (caddr *c-task*))
                        (or (<= (length (setf *c-slot-sibs* (sib-slots *c-slot*)))
                                50)
                            (setf *c-slot-sibs* (list *c-slot*)))
                        (or *c-slot-sibs*
                            (setf *c-slot-sibs* (list *c-slot*)))
                        (some (lambda (z)
                                (cond ((not (listp z))
                                       nil)
                                      ((eq (cadr z) '->)
                                       (setf *c-from* (car z))
                                       (setf *c-to* (caddr z))
                                       t)
                                      (t nil)))
                              (car (last c-t-res))))))
  then-define-new-concepts (lambda (task)
                             (let ((new-unit (create-unit 'h-avoid-2 'h-avoid-2)))
                               ;; TODO - should these subpair names be their earmuffed names?
                               (setproplist new-unit (subpair '(g-slot c-slot c-slot-sibs not-for-real c-from c-to)
                                                              (list *g-slot* *c-slot* *c-slot-sibs* t *c-from* *c-to*)
                                                              (getproplist new-unit)))
                               (setf *new-units* (cdr (assoc 'new-units *task-results*)))
                               (cond (*new-units* (nconc1 *new-units* new-unit))
                                     (t (push (list 'new-units new-unit) *task-results*)))
                               (addprop 'h13 'applics
                                        `((task-num ,*task-num* ,task ,(date))
                                          (,new-unit)
                                          ,(initialize-credit-assignment)
                                          ("Will avoid changing a"
                                           ,*c-from* "inside the" ,*c-slot* ,@(cond ((cdr *c-slot-sibs*)
                                                                                     `(", actually all of these:"
                                                                                       ,*c-slot-sibs* ","))
                                                                                    (t `(",")))
                                           "of units whenever finding" ,*g-slot* "of them")))
                               (dolist (h (setf *creditors* (cdr (assoc 'credit-to *cur-sup*))))
                                 (addprop h 'applics
                                          `((task-num ,*task-num* ,task ,(date))
                                            (,new-unit)
                                            ,(decrement-credit-assignment))))
                               (put new-unit 'creditors (push 'h13 *creditors*)))
                             t)
  applics (((task-num 87 (h1-11 applics) "29-Mar-81 16:36:06")
            (h-avoid-2-and)
            1
            ("Specialized" h-avoid-2 "as follows: " ((c-from -> and)
                                                     (c-to -> the-first-of)
                                                     (c-slot -> if-working-on-task)
                                                     (c-slot-sibs -> (if-potentially-relevant
                                                                      if-truly-relevant
                                                                      if-about-to-work-on-task
                                                                      if-working-on-task
                                                                      if-finished-working-on-task))
                                                     (g-slot -> generalizations)))))
  arity 1)

(defheuristic h14
  isa (hind-sight-rule heuristic op anything)
  english "IF C is about to die, then try to form a new heuristic, one which -- had it existed earlier -- would have prevented C from ever being defined in the first place, by preventing the same losing sort of entity being the replacer"
  if-potentially-relevant (lambda (f)
                            (memb f *deleted-units*))
  worth 700
  abbrev "Form a rule that would have prevented this mistake"
  then-print-to-user (lambda (task)
                       (declare (ignore task))
                       (cprin1 13 "~%~%Just before destroying a losing concept, Eurisko generalized from that bad experience, in the following way: "
                               "Eurisko will no longer change something into " *c-to*
                               " inside any of these " *c-slot-sibs* " slots of a unit when trying to find " *g-slot*
                               " of that unit.  We learned our lesson from " *arg-unit* "~%~%"))
  then-compute (lambda (c)
                 (let ((c-t-res (find-if (lambda (a)
                                           (memb c (cadr a)))
                                         (applics (car (creditors c))))))
                   (and (setf *c-slot*
                              (cadr (assoc 'slot-to-change
                                           (car (cddddr (setf *c-task*
                                                              (caddar c-t-res)))))))
                        (setf *g-slot* (caddr *c-task*))
                        (or (<= (length (setf *c-slot-sibs* (sib-slots *c-slot*)))
                                50)
                            (setf *c-slot-sibs* (list *c-slot*)))
                        (or *c-slot-sibs* (setf *c-slot-sibs* (list *c-slot*)))
                        (some (lambda (z)
                                (cond ((eq (cadr z) '->)
                                       (setf *c-from* (car z))
                                       (setf *c-to* (caddr z))
                                       t)
                                      (t nil)))
                              (car (last c-t-res))))))
  then-define-new-concepts (lambda (task)
                             (let ((new-unit (create-unit 'h-avoid-3 'h-avoid-3)))
                               (setproplist new-unit (subpair '(g-slot c-slot c-slot-sibs not-for-real c-from c-to)
                                                              (list *g-slot* *c-slot* *c-slot-sibs* t *c-from* *c-to*)
                                                              (getproplist new-unit)))
                               (setf *new-units* (cdr (assoc 'new-units *task-results*)))
                               (cond (*new-units* (nconc1 *new-units* new-unit))
                                     (t (push (list 'new-units new-unit) *task-results*)))
                               (addprop 'h14 'applics
                                        `((task-num ,*task-num* ,task ,(date))
                                          (,new-unit)
                                          ,(initialize-credit-assignment)
                                          ("Will avoid changing anything into a"
                                           ,*c-to* "inside the" ,*c-slot* "slot"
                                           ,@(cond ((cdr *c-slot-sibs*)
                                                    `(", actually all of these:" ,*c-slot-sibs* ","))
                                                   (t '(",")))
                                           "of units whenever finding" *g-slot* "of them")))
                               (dolist (h (setf *creditors* (cdr (assoc 'credit-to *cur-sup*))))
                                 (addprop h 'applics
                                          `((task-num ,*task-num* ,task ,(date))
                                            (,new-unit)
                                            ,(decrement-credit-assignment))))
                               (put new-unit 'creditors (push 'h14 *creditors*)))
                             t)
  applics (((task-num 87 (h1-11 applics) "29-mar-81 16:36:33")
             (h-avoid-3-first)
             1
             ("Specialized" h-avoid-3 "as follows: " ((c-from -> and)
                                                      (c-to -> the-first-of)
                                                      (c-slot -> if-working-on-task)
                                                      (c-slot-sibs -> (if-potentially-relevant
                                                                       if-truly-relevant
                                                                       if-about-to-work-on-task
                                                                       if-working-on-task
                                                                       if-finished-working-on-task))
                                                      (g-slot -> generalizations)))))
  arity 1)

(defheuristic h15
  isa (heuristic op anything)
  english "IF the current task is to find examples of a unit, and it is the range of some operation f, THEN gather together the outputs of the I/O pairs stored on Applics of f"
  if-potentially-relevant null
  worth 700
  abbrev "If C is Range (f), then Exs (C) can be gotten from Applics (f)"
  if-working-on-task (lambda (task)
                       (declare (ignore task))
                       (and (eq *cur-slot* 'examples)
                            (setf *ops-to-use* (is-range-of *cur-unit*))))
  then-print-to-user (lambda (task)
                       (declare (ignore task))
                       (cprin1 13 "~%Instantiated " *cur-unit* "; there are now "
                               (length (examples *cur-unit*)) " " 'examples "~%")
                       (cprin1 48 "    The new ones are: " *new-values* "~%")
                       t)
  then-compute (lambda (task)
                 (declare (ignore task))
                 (setf *cur-val* (funcall *cur-slot* *cur-unit*))
                 (and (setf *space-to-use* (map-union *ops-to-use* 'applics))
                      (dolist (z *space-to-use*)
                        (setf z (extract-output z))
                        (and (not (member z (examples *cur-unit*)))
                             (not (member z (non-examples *cur-unit*)))
                             (cprin1 58 "+")
                             (union-prop *cur-unit* 'examples z))))
                 (and (setf *new-values* (set-difference (examples *cur-unit*) *cur-val*))
                      (push `(new-values
                              (,*cur-unit* ,*cur-slot* ,*new-values*
                                           ("By examining Applics of"
                                            ,*ops-to-use* ", Eurisko found" ,(length *new-values*)
                                            "examples of" ,*cur-unit*)))
                            *task-results*))
                 ;; ORIG: this always returns T; if the SpaceToUse was null, then
                 ;;       ThenAddToAgenda will want to add a task to the agenda to help
                 ;;       correct that situation
                 t)
  then-add-to-agenda (lambda (task)
                       (declare (ignore task))
                       (cond (*space-to-use* ;; ORIG: There were some Applics of OpToUse
                              t)
                             (t (add-to-agenda `((,(floor *cur-pri* 2)
                                                  ,*cur-unit* ,*cur-slot* (("Had to suspend whilst gathering applics of"
                                                                            ,*ops-to-use*)
                                                                           ,(car *cur-reasons*))
                                                  ,*cur-sup*
                                                  ,@ (mapcar (lambda (otu)
                                                               `(,(1- *cur-pri*)
                                                                 ,otu applics
                                                                 (("Recent task was stymied for lack of such applics; namely, tryign to find Examples of"
                                                                   ,*cur-unit*)
                                                                  ((credit-to h15)))))
                                                             *ops-to-use*))))
                                (add-task-results 'new-tasks
                                                  `(,(length *ops-to-use*)
                                                    "task to find Applics of" ,*ops-to-use*
                                                    "and 1 task just like the current one"))
                                (cprin1 40 "~%Hmmm... can't proceed with this until some Applics of "
                                        *ops-to-use* " are known.~%")
                                nil)))
  then-compute-record (5368 . 7)
  then-add-to-agenda-failed-record (3302 . 3)
  then-add-to-agenda-record (36 . 4)
  then-print-to-user-record (1201 . 4)
  overall-record (7825 . 4)
  arity 1)

(defheuristic h16
  isa (heuristic anything op)
  english "IF the results of performing f are sometimes (at least one time in ten) useful, THEN consider creating new generalizations of f"
  if-potentially-relevant (lambda (f)
                            ;; ORIG: check that f has some recorded applications -- which
                            ;;       implies, of course, that f is an executable/performable entity
                            (applics f))
  if-truly-relevant (lambda (f)
                      ;; ORIG: check that some Applics of f have high Worth, but most have low Worth
                      ;; ORIG: the extent to which these conditions are met will
                      ;;       determine the amoun of energy to expend working on
                      ;;       applying this rule -- its overall relevancy
                      ;; TODO - lambda was quoted, I think it's equivalent to have it unquoted,
                      ;;        unless it NEEDED some interpreter-specific feature?
                      (and (some (lambda (a)
                                   ;; ORIG: this will have the format (args results)
                                   (some #'has-high-worth (cadr a)))
                                 (applics f))
                           (> (setf *fraction* (fraction-of (map-union (applics f) #'cadr)
                                                            'has-high-worth))
                              0.1)
                           (not (subsumed-by f))))
  worth 600
  abbrev "Generalize a sometimes-useful action"
  then-print-to-user (lambda (f)
                       (cprin1 13 "~%" *conjec* ":~%Since some applications of " f " (i.e., " (abbrev f)
                               ") are very valuable, so EURISKO wants to find new concepts which are slightly more generalized than "
                               f ", and (to that end) has added a new task to the agenda to find such concepts. ")
                       t)
  then-conjecture (lambda (f)
                    (push (progn
                            (setf *conjec* (new-name 'conjec))
                            (create-unit *conjec* 'proto-conjec)
                            (put *conjec* 'english
                                 `("Generalizations of"
                                   ,f "may be very valuable in the long run, since it already has some good applications"
                                   "(" ,(percentify *fraction*) "are winners)"))
                            (put *conjec* 'abbrev `(,f "sometimes wins, so generalizations of it may be very big winners"))
                            (put *conjec* 'worth (average-worths 'h16 f)))
                          *conjectures*))
  then-add-to-agenda (lambda (f)
                       (add-to-agenda `((,(average-worths f 'h16)
                                         ,f 'generalizations
                                         (,*conjec*)
                                         ((credit-to h16)))))
                       ;; TODO - rename this add-task-property
                       (add-task-results 'new-tasks '("1 unit must be generalized")))
  then-conjecture-record (653 . 4)
  then-add-to-agenda-record (90 . 4)
  then-print-to-user-record (622 . 4)
  overall-record (1756 . 4)
  arity 1)

(defheuristic h17
  isa (heuristic anything op)
  english "IF the current task is to generalize a unit, and no general slot has been chosen to be the one changed, THEN randomly select which slots to generalize"
  if-potentially-relevant null
  worth 600
  abbrev "Generalize u by generalizing some random slots"
  if-working-on-task (lambda (task)
                       (declare (ignore task))
                       (and (is-a-kind-of *cur-slot* 'generalizations)
                            (null (assoc 'slot-to-change *cur-sup*))
                            (>= 7 (the-number-of *agenda* (lambda (z)
                                                            (and (eq *cur-unit* (extract-unit-name z))
                                                                 (eq *cur-slot* (extract-slot-name z))))))))
  then-print-to-user (lambda (task)
                       (declare (ignore task))
                       (cprin1 13 "~%" *cur-unit* "will be generalized by generalizing the following of its slots:"
                               *slots-to-change* "~%~%")
                       t)
  then-add-to-agenda (lambda (task)
                       (declare (ignore task))
                       (add-to-agenda (sort (mapcar (lambda (s)
                                                      `(,(average *cur-pri* (average-worths s 'h17))
                                                        ,*cur-unit* ,*cur-slot*
                                                        (,(setf *new-reason*
                                                                (list "A new unit will be created by generalizing the"
                                                                      s "slot of" *cur-unit*)))
                                                        ((slot-to-change ,s)
                                                         (credit-to h17 ,@*credit-to*))))
                                                    *slots-to-change*)
                                            #'order-tasks))
                       (add-task-results 'new-tasks
                                         `(,(length *slots-to-change*)
                                           "specific slots of" ,*cur-unit* "to find" ,*cur-slot* "of")))
  then-compute (lambda (task)
                 (declare (ignore task))
                 (setf *slots-to-change* (random-subset (set-intersect (slot-names *cur-unit*)
                                                                       (examples 'slot))))
                 (setf *credit-to* (cdr (assoc 'credit-to *cur-sup*)))
                 t)
  then-compute-record (430 . 4)
  then-add-to-agenda-record (688 . 4)
  then-print-to-user-record (435 . 4)
  overall-record (1943 . 4)
  arity 1)

(defheuristic h18
  isa (heuristic anything op)
  english "IF the current task is to generalize a unit, and a slot has been chosen to be the one changed, THEN randomly select a part of it and generalize that part"
  if-potentially-relevant null
  worth 704
  abbrev "Generalize a given slot of a given unit"
  if-working-on-task (lambda (task)
                       (declare (ignore task))
                       (and (is-a-kind-of *cur-slot* 'generalizations)
                            (setf *slot-to-change* (cadr (assoc 'slot-to-change *cur-sup*)))))
  then-print-to-user (lambda (task)
                       (declare (ignore task))
                       (cprin1 13 "~%Generalized the " *slot-to-change* " slot of "
                               *cur-unit* ", replacing its old value ")
                       (cprin1 48 "(which was " *old-value* ") ")
                       (cprin1 14 "by " *new-value* ".~%")
                       (cprin1 13 "~%")
                       t)
  then-compute (lambda (task)
                 (declare (ignore task))
                 ;; ORIG: assumes the existence of functions GeneralizeLispPred
                 ;;       GeneralizeLispFn GeneralizeListr and of course GeneralizeNIL to catch
                 ;;       the slots which have not DataType slot
                 ;; TODO - check to see if any of these are just locals
                 (setf *u-diff* nil)
                 (setf *are-units* nil)
                 (setf *have-genl* nil)
                 (setf *new-value* (funcall (pack* 'generalize- (data-type *slot-to-change*))
                                            (setf *old-value* (funcall *slot-to-change* *cur-unit*))))
                 (let ((need-genl (set-diff *are-units* *have-genl*)))
                   ;; ORIG: If the OldValue and NewValue are equal, then we really8 ahven't
                   ;;       generalized it at all, so we want to return NIL and have this rule FAIL
                   (mapc #'tiny-reward *have-genl*)
                   (and *have-genl*
                        (add-task-results 'rewarded-units `(,*have-genl*
                                                            "because they could have been used in generalizing"
                                                            ,*cur-unit*)))
                   (add-to-agenda (mapcar (lambda (ns)
                                            `(,(half *cur-pri*)
                                              ,ns
                                              generalizations
                                              ((,*cur-unit* "might have been generalized better, earlier, if some generalizations had existed for"
                                                            ,ns))
                                              ((credit-to h18))))
                                          need-genl))
                   (and need-genl
                        (add-task-results 'new-tasks (list need-genl "will be generalized, because if such generalizations had existed, we could have used them just now while trying to generalize" *cur-unit*))))
                 (cond ((equal *old-value* *new-value*)
                        (cprin1 15 "~%Hmmm... couldn't seem to find any meaningful generalization of the "
                                *slot-to-change* " slot of " *cur-unit* "~%")
                        nil)
                       ((> *verbosity* 15)
                        (cprin1 15 "~%Inside the " *slot-to-change* " slot, ")
                        (maprint *u-diff*)
                        (terpri)
                        t)
                       (t t)))
  then-define-new-concepts (lambda (task)
                             (let ((new-unit (create-unit *cur-unit* *cur-unit*)))
                               (dolist (s (sib-slots *slot-to-change*))
                                 (lambda (s)
                                   (kill-slot new-unit s)))
                               (put new-unit *slot-to-change* *new-value*)
                               (setf *new-units* (cdr (assoc 'new-units *task-results*)))
                               (cond (*new-units* (nconc1 new-unit *new-units*))
                                     (t (push (list 'new-units new-unit) *task-results*)))
                               (addprop 'h18 'applics
                                        `((task-num ,*task-num* ,task ,(date))
                                          (,new-unit)
                                          ,(initialize-credit-assignment)
                                          ("Generalized" ,*slot-to-change* "slot of" *cur-unit* "as follows:" *u-diff*)))
                               (dolist (h (setf *creditors* (cdr (assoc 'credit-to *cur-sup*))))
                                 (addprop h 'applics
                                          `((task-num ,*task-num* ,task ,(date))
                                            (,new-unit)
                                            ,(decrement-credit-assignment))))
                               (put new-unit 'creditors (push 'h18 *creditors*))
                               (addprop *cur-unit* 'generalizations new-unit)
                               (addprop new-unit 'specializations *cur-unit*))
                             t)
  then-compute-failed-record (5658 . 17)
  then-compute-record (3974 . 13)
  then-define-new-concepts-record (5740 . 13)
  then-print-to-user-record (2147 . 13)
  overall-record (13078 . 13)
  arity 1)

(defheuristic h19
  isa (heuristic op anything)
  english "IF we just created some new units, THEN eliminate any whose slots are equivalent to already-extant units"
  if-potentially-relevant null
  worth 150
  abbrev "Kill any new unit that's the same as an existing one"
  if-finished-working-on-task (lambda (task)
                                (declare (ignore task))
                                (and *new-units*
                                     (assoc 'new-units *task-results*)
                                     (setf *doomed-u*
                                           (subset *new-units*
                                                   (lambda (u)
                                                     (some (lambda (z)
                                                             ;; ORIG: See if U and Z are equivalent units
                                                             (every (intersection (propnames u)
                                                                                  (examples 'slot))
                                                                    (lambda (p)
                                                                      (equal-to-within-subst u z
                                                                                             (funcall p u)
                                                                                             (funcall p z)))))
                                                           (delete u (map-union (isa u) 'examples))))))))
  then-print-to-user (lambda (c)
                       (declare (ignore c))
                       (cprin1 14 "~%Hmf~ " (length *doomed-u*) " of the " (length *new-units*)
                               " new units (namely: " *doomed-u* ") seem indistinguishable from pre-existing units!"
                               "  They must be destroyed...~%")
                       (setf *new-units* (set-diff *new-units* *doomed-u*))
                       t)
  then-delete-old-concepts (lambda (c)
                             (declare (ignore c))
                             (mapc #'kill-unit *doomed-u*)
                             t)
  applics (((sit1)
            (win1 los1))
           ((sit2)
            (los2 los3 los4 los5 los6)))
  subsumed-by (h19-criterial)
  arity 1)

(defheuristic h19-criterial
  isa (heuristic op anything)
  english "IF we just created some new units, THEN eliminate any whose criterial slots are equivalent to already-extant units"
  if-potentially-relevant null
  worth 700
  abbrev "Kill any new unit which duplicates an already-existing one"
  if-finished-working-on-task (lambda (task)
                                (declare (ignore task))
                                (and *new-units*
                                     (assoc 'new-units *task-results*)
                                     (setf *doomed-u* (subset *new-units*
                                                              (lambda (u)
                                                                (some (lambda (z)
                                                                        ;; ORIG: See if U and Z are equivalent units
                                                                        (every (intersection (propnames u)
                                                                                             (examples 'criterial-slot))
                                                                               (lambda (p)
                                                                                 (equal-to-within-subst u z
                                                                                                        (funcall p u)
                                                                                                        (funcall p z)))))
                                                                      (union (cons *cur-unit*
                                                                                   (getprop *cur-unit* 'specializations))
                                                                             (delete u (map-union (isa u) #'examples)))))))))
  then-print-to-user (lambda (c)
                       (declare (ignore c))
                       (cprin1 14 "~%Hmf! " (length *doomed-u*) " of the " (length *new-units*) " new units "
                               "(namely: " *doomed-u* ") have criterial slots that seem indistinguishable from pre-existing units!"
                               "  They must be destroyed...~%")
                       (setf *new-units* (set-diff *new-units* *doomed-u*))
                       t)
  then-delete-old-concepts (lambda (c)
                             (declare (ignore c))
                             (mapc #'kill-unit *doomed-u*)
                             t)
  subsumes (h19)
  creditors (h6 h5 h1)
  then-delete-old-concepts-record (45416 . 52)
  then-print-to-user-record (10904 . 52)
  overall-record (69884 . 52)
  arity 1)

(defheuristic h20
  isa (heuristic op anything)
  english "IF an op f (e.g., a math function, a heuristic, a slot) can apply to any of the domain items of another op, THEN so apply it and maybe some patterns will emerge"
  if-potentially-relevant (lambda (f)
                            ;; TODO - make this an actual slot describing F, instead of implying it all the time?
                            ;; ORIG: check that f has some recorded applications -- which
                            ;;       implies, of course, that f is an
                            ;;       executable/performable entity
                            (setf *alg-to-use* (alg f)))
  if-truly-relevant (lambda (f)
                      ;; ORIG: check that some Applics of f have high Worth, but most have low Worth
                      ;; ORIG: the extent to which those conditions are met will
                      ;;       determine the amount of energy to expend working on
                      ;;       applying this rule -- its overall relevancy
                      (and (not (subsumed-by f))
                           (setf *space-to-use* (subset (remove f (sibs f))
                                                        (lambda (f2)
                                                          (and (eq (arity f)
                                                                   (arity f2))
                                                               (> (length (applics f2)) 3)))))
                           (setf *domain-tests* (mapcar #'defn (domain f)))))
  worth 600
  abbrev "Run f on args used for other ops"
  then-print-to-user (lambda (f)
                       (cprin1 14 "~%" f "'s algorithm has been run on new data upon which these have already been run: "
                               *added-some* "~% We will sometime look for connections between " f
                               " and each of those other operartions.~%")
                       t)
  then-add-to-agenda (lambda (f)
                       (add-to-agenda (mapcar (lambda (f2)
                                                (list (average-worths f2 (average-worths f 'h20))
                                                      f
                                                      'conjectures
                                                      `((,f "has now been run on the same data as"
                                                            ,f2 ", and we should investigate any patters connecting them"))
                                                      `((credit-to h20)
                                                        (involved-units (,f2)))))
                                              *added-some*))
                       (add-task-results 'new-tasks
                                         `(,(length *added-some*) "units may have connections to current one")))
  then-compute (lambda (f)
                 (setf *added-some* nil)
                 (dolist (f2 *space-to-use*)
                   (dolist (ap (applics f2))
                     (and (not (known-applic f (car ap)))
                          ;; TODO - unravel this
                          (every #'funcall *domain-tests* (car ap))
                          (union-prop f 'applics (list (car ap) (apply *alg-to-use* (car ap))))
                          (pushnew f2 *added-some* :test #'eq))))
                 *added-some*)
  arity 1
  then-compute-failed-record (5828 . 14)
  then-compute-record (-546691 . 16)
  then-add-to-agenda-record (5355 . 16)
  overall-record (-528368 . 16))

(defheuristic h21
  isa (heuristic op anything)
  english "IF an op u duplicates all the results of u2, THEN conjecture that u is an extension of u2"
  if-potentially-relevant null
  worth 400
  abbrev "See if u is an extension of u2"
  if-working-on-task (lambda (task)
                       (declare (ignore task))
                       (and (is-a-kind-of *cur-slot* 'conjectures)
                            (setf *involved-units* (cadr (assoc 'involved-units *cur-sup*)))))
  then-print-to-user (lambda (task)
                       (declare (ignore task))
                       (cprin1 13 "~%Apparently " *cur-unit* " is an extension of " *res-u* "~%")
                       t)
  then-conjecture (lambda (task)
                    (declare (ignore task))
                    (dolist (u2 *res-u*)
                      (push (progn
                              (setf *conjec* (new-name 'conjec))
                              (create-unit *conjec* 'proto-conjec)
                              (put *conjec* 'english
                                   `("All applics of" ,u2 "are also applics of " ,*cur-unit*
                                                      ", so we presume that " ,*cur-unit*
                                                      "is an extension of" ,u2))
                              (put *conjec* 'abbrev `(,*cur-unit* "appears to be an extension of" ,u2))
                              (put *conjec* 'worth (floor (average (average-worths 'h21 (average-worths *cur-unit* u2))
                                                                   (min 1000 (floor (* 100.0 (log (length (applics u2)))))))))
                              (put *conjec* 'conjecture-about (list *cur-unit* u2))
                              *conjec*)
                            *conjectures*)
                      (union-prop u2 'conjectures *conjec*)
                      (union-prop *cur-unit* 'conjectures *conjec*)
                      (union-prop *cur-unit* 'restrictions u2)
                      (union-prop u2 'extensions *cur-unit*))
                    *res-u*)
  then-compute (lambda (task)
                 (declare (ignore task))
                 (setf *res-u* (subset *involved-units*
                                       (lambda (u2)
                                         (and (applics u2)
                                              (is-subset-of (applics u2)
                                                            (applics *cur-unit*)))))))
  arity 1
  then-compute-failed-record (805 . 18)
  then-compute-record (3584 . 2)
  then-conjecture-record (3055 . 2)
  then-print-to-user-record (287 . 2)
  overall-record (11576 . 2))

(defheuristic h22
  isa (heuristic op anything)
  english "IF instances of a unit have been found, THEN place a task on the Agenda to see if any of them are unusually interesting"
  if-potentially-relevant null
  worth 500
  abbrev "Check instances of a unit for gems"
  if-finished-working-on-task (lambda (task)
                                (declare (ignore task))
                                (and (is-a-kind-of *cur-slot* (instances *cur-unit*))
                                     (interestingness *cur-unit*)
                                     (funcall *cur-slot* *cur-unit*)))
  then-print-to-user (lambda (task)
                       (declare (ignore task))
                       (cprin1 13 "A new task was added to the agenda, to see which of the "
                               (length (examples *cur-unit*))
                               " are interesting ones.~%")
                       t)
  then-add-to-agenda  (lambda (task)
                        (declare (ignore task))
                        (add-to-agenda `((,(average-worths *cur-unit* 'h22)
                                          ,*cur-unit*
                                          ,(car (more-interesting (instances *cur-unit*)))
                                          ("Now that instances of a unit have been found, see if any are unusually interesting")
                                          (credit-to h22))))
                        (add-task-results 'new-tasks '("1 unit's instances must be evaluated for Interestingness")))
  arity 1
  then-add-to-agenda-record (14 . 1)
  then-print-to-user-record (38 . 1)
  overall-record (75 . 1))

(defheuristic h23
  isa (heuristic op anything)
  english "IF the current task is to find interesting examples of a unit, and it has some known examples already, THEN look over examples of the unit, and see if any of them are interesting"
  if-potentially-relevant null
  worth 700
  abbrev "Some exs (u) may be interesting"
  if-working-on-task (lambda (task)
                       (declare (ignore task))
                       (and (is-a-kind-of *cur-slot* 'int-examples)
                            (setf *defn-to-use* (interestingness *cur-unit*))
                            (setf *space-to-use* (examples *cur-unit*))))
  then-print-to-user (lambda (task)
                       (declare (ignore task))
                       (cprin1 13 "~%Found " (length *new-values*) " of the " (length (examples *cur-unit*)) " to be interesting.~%")
                       (cprin1 48 "    Namely: " *new-values* "~%")
                       t)
  then-compute (lambda (task)
                 (declare (ignore task))
                 (setf *cur-val* (funcall *cur-slot* *cur-unit*))
                 (dolist (z *space-to-use*)
                   (if (funcall *defn-to-use* z)
                       (progn
                         (cprin1 55 "+")
                         (union-prop *cur-unit* 'int-examples z)
                         t)
                       (progn
                         (cprin1 56 "-")
                         nil)))
                 (when (setf *new-values* (set-difference (funcall *cur-slot* *cur-unit*)
                                                         *cur-val*))
                   (add-task-results 'new-values
                                     `(,*cur-unit*
                                       ,*cur-slot*
                                       ,*new-values*
                                       ("By examining Examples of" ,*cur-unit* ", Eurisko found"
                                                                   ,(length *new-values*) " of them were also "
                                                                   ,*cur-slot* " of " ,*cur-unit*)))))
  arity 1)

(defheuristic h24
  isa (heuristic op anything)
  english "IF trying to see if a category is interesting, THEN see if all its examples satisfy the same, interesting, preferably rare predicate"
  if-potentially-relevant (lambda (f)
                            ;; ORIG: Note this is one of the rare rules which is used both to
                            ;;       see if a unit f is interesting, via WorkOnUnit and via
                            ;;       WorkOnTask
                            (and (memb 'category (isa f))
                                 (setf *space-to-use* (subset (examples 'unary-pred)
                                                              (lambda (p)
                                                                (and (or (has-high-worth p)
                                                                         (memb p (int-examples 'unary-pred)))
                                                                     (leq-nn (car (rarity p))
                                                                             0.3)))))
                                 (>= (length (examples *cur-unit*))
                                     4)
                                 (setf *cur-unit* f)
                                 (setf *cur-slot* 'why-int)))
  worth 500
  abbrev "See if all examples of a category satisfy the same intereting predicate"
  if-working-on-task (lambda (task)
                       (declare (ignore task))
                       (and (is-a-kind-of *cur-slot* 'why-int)
                            (memb 'category (isa *cur-unit*))
                            (setf *space-to-use* (subset (examples 'unary-pred)
                                                         (lambda (p)
                                                           (and (or (has-high-worth p)
                                                                    (memb p (int-examples 'unary-pred)))
                                                                (leq-nn (car (rarity p))
                                                                        0.3)))))
                            (>= (length (examples *cur-unit*))
                                4)))
  then-print-to-user (lambda (task)
                       (declare (ignore task))
                       (cprin1 13 "~%Of the " (length *space-to-use*)
                               " predicates we tried, " (length *reas*)
                               " were found to hold on all examples of " *cur-unit*
                               ", thereby making it interesting.~%")
                       (cprin1 40 "    Namely, " *reas* "~%")
                       t)
  then-compute (lambda (task)
                 (declare (ignore task))
                 (setf *reas* (subset *space-to-use*
                                      (lambda (p)
                                        ;; ORIG: See if all examples of CurUnit
                                        ;;       satisfy predicate P
                                        (every (lambda (x)
                                                 (run-alg p x))
                                               (examples *cur-unit*)))))
                 (union-prop-l *cur-unit* *cur-slot* *reas*)
                 *reas*)
  arity 1)

(defheuristic h25
  isa (heuristic anything op)
  english "IF the unit being focused on is a very interesting predicate, THEN study the set of tuples upon which it holds"
  if-potentially-relevant (lambda (f)
                            (and (memb 'pred (isa f))
                                 (or (has-high-worth f)
                                     (is-a-int f))))
  worth 500
  abbrev "Define the set of tuples satisfying a given predicate"
  arity 1
  ;; Parameter used to be TASK, but it makes more sense as F
  then-print-to-user (lambda (f)
                       (cprin1 13 "~%Defined the set of entities satisfying predicate " f "~%")
                       (cprin1 41 "	I.e., those lists whose format is " f ", and which cause " f " to return a non-null value.~%"))
  then-define-new-concepts (lambda (f)
                             (let ((new-unit (create-unit (pack* 'satisfying-set-for- f))))
                               ;; Original didn't have Worth quoted, probably a bug
                               (put new-unit 'worth (average-worths f 'h25))
                               (add-task-results 'new-units new-unit)
                               (addprop 'h25 'applics
                                        `((task-num ,*task-num* ,*task* ,(date))
                                          (,new-unit)
                                          ,(initialize-credit-assignment)
                                          ("Defined satisfying set for predicate" ,f)))
                               (dolist (h (setf *creditors* (cdr (assoc 'credit-to *cur-sup*))))
                                 (addprop h 'applics
                                          `((task-num ,*task-num* ,*task* ,(date))
                                            (,new-unit)
                                            ,(decrement-credit-assignment))))
                               (put new-unit 'creditors (push 'h25 *creditors*))
                               (put new-unit 'generalizations (cons 'list
                                                                    (copy (generalizations 'list))))
                               (put new-unit 'isa (copy (isa 'list)))
                               (put new-unit 'fast-defn `(lambda (l)
                                                           (and (run-defn 'list l)
                                                                (eq (length l)
                                                                    ,(length (domain f)))
                                                                ,@(mapcar (lambda (d cr)
                                                                            `(run-defn ',d ,(list cr 'l)))
                                                                          (domain f)
                                                                          '(first second third fourth fifth sixth seventh))
                                                                (apply-alg ',f l))))
                               (add-inv new-unit))
                             t))

(defheuristic h26
  isa (heuristic anything op)
  english "IF the unit being focused on is a very interesting predicate, THEN study the set of tuples upon which it fails to hold"
  if-potentially-relevant (lambda (f)
                            (and (memb 'pred (isa f))
                                 (or (has-high-worth f)
                                     (is-a-int f))))
  worth 500
  abbrev "Define the set of tuples failing to satisfy a given predicate"
  arity 1
  ;; Parameter was TASK, but makes more sense as F
  then-print-to-user (lambda (f)
                       (cprin1 13 "~%Defined the set of entities failing to satisfy predicate " f "~%")
                       (cprin1 41 "	I.e., those lists whose format is " (domain f)
                               ", and which cause " f " to return a null value.~%"))
  then-define-new-concepts (lambda (f)
                             (let ((new-unit (create-unit (pack* 'failing-set-for- f))))
                               ;; Same issues with WORTH and TASK/F as H25
                               (put new-unit 'worth (average-worths f 'h26))
                               (add-task-results 'new-units new-unit)
                               (addprop 'h26 'applics
                                        (list (list 'task-num *task-num* *task* (date))
                                              (list new-unit)
                                              (decrement-credit-assignment)
                                              (list "Defined failing set for predicate" f)))
                               (dolist (h (setf *creditors* (cdr (assoc 'credit-to *cur-sup*))))
                                 (addprop h 'applics
                                          (list (list 'task-num *task-num* *task* (date))
                                                (list new-unit)
                                                (decrement-credit-assignment))))
                               (put new-unit 'creditors (push 'h26 *creditors*))
                               (put new-unit 'generalizations (cons 'list
                                                                    (copy (generalizations 'list))))
                               (put new-unit 'isa (copy (isa 'list)))
                               (put new-unit 'fast-defn `(lambda (l)
                                                           (and (run-defn 'list l)
                                                                (eq (length l)
                                                                    ,(length (domain f)))
                                                                ,@(mapcar (lambda (d cr)
                                                                            `(run-defn ',d (,cr 'l)))
                                                                          (domain f)
                                                                          '(first second third forth fifth sixth seventh))
                                                                (memb (apply-alg ',f l) *failure-list*))))
                               (add-inv new-unit))
                             t))

(defheuristic h27
  isa (heuristic anything op)
  english "IF the unit being focused on is a very interesting unary predicate, THEN study the set of items upon which it holds"
  if-potentially-relevant (lambda (f)
                            (and (memb 'unary-pred (isa f))
                                 (or (has-high-worth f)
                                     (is-a-int f))))
  worth 500
  abbrev "Define the se of domain elements satisfying a given unary predicate"
  arity 1
  ;; Parameter was TASK, makes more sense as F
  then-print-to-user (lambda (f)
                       (cprin1 13 "~%Defined the subcategory of " (car (domain f))
                               "s which satisfy the unary predicate " f "~%"))
  then-define-new-concepts (lambda (f)
                             (let ((new-unit (create-unit (pack* 'satisfying-set-for- f))))
                               ;; Same issues as h25 with WORTH and TASK vs F
                               (put new-unit 'worth (average-worths f 'h27))
                               (add-task-results 'new-units new-unit)
                               (addprop 'h27 'applics
                                        (list (list 'task-num *task-num* *task* (date))
                                              (list new-unit)
                                              (initialize-credit-assignment)
                                              ;; TODO - PACK* was quoted?
                                              (list "Defined satisfying" (pack* (car (domain f)) 's)
                                                    "for unary predicate" f)))
                               (dolist (h (setf *creditors* (cdr (assoc 'credit-to *cur-sup*))))
                                 (addprop h 'applics
                                          (list (list 'task-num *task-num* *task* (date))
                                                (list new-unit)
                                                (decrement-credit-assignment))))
                               (put new-unit 'creditors (push 'h27 *creditors*))
                               (put new-unit 'generalizations (cons '(car (domain f))
                                                                    (copy (generalizations '(car (domain f))))))
                               (put new-unit 'isa (copy (isa '(car (domain f)))))
                               (put new-unit 'fast-defn `(lambda (e)
                                                           (run-defn ,(car (domain f)) e)))
                               (add-inv new-unit))
                             t))

(defheuristic h28
  isa (heuristic anything op)
  english "IF the unit being focused on is a very interesting unary predicate, THEN study the set of items upon which it fails to hold"
  if-potentially-relevant (lambda (f)
                            (and (memb 'unary-pred (isa f))
                                 (or (has-high-worth f)
                                     (is-a-int f))))
  worth 500
  abbrev "Define the set of domain elements failing a given unary predicate"
  arity 1
  ;; Parameter was TASK, makes more sense as F
  then-print-to-user (lambda (f)
                       (cprin1 13 "~%Defined the subcategory of " (car (domain f))
                               "s which fail to satisfy the unary predicate " f "~%"))
  then-define-new-concepts (lambda (f)
                             (let ((new-unit (create-unit (pack* 'failing-set-for- f))))
                               ;; Same issues with WORTH as H25
                               (put new-unit 'worth (average-worths f 'h28))
                               (add-task-results 'new-units new-unit)
                               (addprop 'h28 'applics
                                        ;; TODO - this needs to be an ADD-APPLIC form
                                        (list (list 'task-num *task-num* *task* (date))
                                              (list new-unit)
                                              (initialize-credit-assignment)
                                              ;; TODO - the PACK* form was quoted in the original, probably didn't print right?
                                              (list "Defined failing" (pack* (car (domain f)) 's) "for unary predicate" f)))
                               (dolist (h (setf *creditors* (cdr (assoc 'credit-to *cur-sup*))))
                                 (addprop h 'applics
                                          (list (list 'task-num *task-num* *task* (date))
                                                (list new-unit)
                                                (decrement-credit-assignment))))
                               (put new-unit 'creditors (push 'h28 *creditors*))
                               ;; TODO - why a defensive copy? are destructive operations on Generalizations done?
                               ;; TODO - what's with the quoting?
                               (put new-unit 'generalizations (cons '(car (domain f))
                                                                    (copy (generalizations '(car (domain f))))))
                               (put new-unit 'isa (copy (isa '(car (domain f)))))
                               (put new-unit 'fast-defn `(lambda (e)
                                                           (and (run-defn ,(car (domain f)) e)
                                                                (memb (run-alg ,f e) *failure-list*))))
                               (add-inv new-unit))
                             t))
(defheuristic h29
  isa (heuristic op anything)
  english "IF the current task is to find examples of a structure which can have multiple elements, and some are known already, THEN get new ones by mutating the multiplicities of some of the elements of those known structures"
  if-potentially-relevant null
  worth 500
  abbrev "New examples of a kind of MultEleStruc can be found by permuting multiplicities of elements of already-known examples"
  ;; TODO - determine which functional slot return values are meaningful, convert ANDs to WHENs etc for those that aren't
  if-working-on-task (lambda (task)
                       (declare (ignore task))
                       (and (is-a-kind-of *cur-unit* 'mult-ele-struc)
                            (is-a-kind-of *cur-slot* 'examples)
                            (setf *space-to-use* (setf *cur-val* (funcall *cur-slot* *cur-unit*)))))
  if-finished-working-on-task (lambda (task)
                                (declare (ignore task))
                                (and (is-a-kind-of *cur-unit* 'mult-ele-struc)
                                     (is-a-kind-of *cur-slot* 'examples)
                                     (setf *space-to-use* (setf *cur-val* (funcall *cur-slot* *cur-unit*)))))
  then-print-to-user (lambda (task)
                       (declare (ignore task))
                       (cprin1 13 "~%Modified multiplicities of elements of examples of " *cur-unit*
                               "s and as a result added " (length *new-values*) " new examples.~%")
                       (cprin1 48 "     Namely: " *new-values* "~%")
                       t)
  then-compute (lambda (task)
                 (declare (ignore task))
                 (dolist (ex *space-to-use*)
                   (let ((ex2 (copy-list ex)))
                     (dolist (e (copy-list ex))
                       (cond ((randomp) nil)
                             ((randomp) (setf ex2 (run-alg 'mult-ele-struc-insert e ex2)))
                             ((randomp) (setf ex2 (run-alg 'mult-ele-struc-delete-1 e ex2)))
                             (t nil)))
                     (union-prop *cur-unit* *cur-slot* ex2)))
                 (and (setf *new-values* (set-difference (examples *cur-unit*) *cur-val*))
                      ;; TODO - convert to PUSH?
                      (setf *task-results* (cons (list 'new-values
                                                       (list *cur-unit* *cur-slot* *new-values*
                                                             (list "By changing multiplicities of elements of examples of"
                                                                   *cur-unit* "Eurisko may have doubled the number of such examples")))
                                                 *task-results*))))
  arity 1)




;;-----------------------
;; H-AVOID heuristics

(defheuristic h-avoid
  isa (heuristic op anything)
  english "IF the current task is to find GSlot of some unit, then make sure that the slot to change isn't any of these: CSlotSibs"
  if-potentially-relevant null
  worth 700
  abbrev ("Avoid GSlot created by altering CSlotSibs")
  if-about-to-work-on-task (lambda (task)
                             (declare (ignore task))
                             (and *not-for-real*
                                  ;; TODO - verify our usage of g-slot/c-slot vs gslot/cslot
                                  (is-a-kind-of *cur-slot* 'g-slot)
                                  (eq (cadr (assoc 'slot-to-change *cur-sup*))
                                      'c-slot)))
  then-print-to-user (lambda (task)
                       (declare (ignore task))
                       (cprin1 14 "~%Hm; I have had bad experiences in the past trying to find " 'g-slot
                               " of units by altering their " 'c-slot
                               " slot, and this is similar; "
                               " I'm just going to abort this entire task!~%")
                       ;; TODO - the literal value should lose the exclamation mark, as the test checks for 'abort-task
                       (setf *abort-task?* 'abort-task!))
  arity 1)

(defheuristic h-avoid-2
  isa (heuristic op anything)
  english "IF the current task is to find GSlot of some unit, then and we did that by altering its CSlot slot, (or ANY of these slots: CSlotSibs) then make sure we didn't change a CFrom into anything"
  if-potentially-relevant null
  worth 700
  abbrev "Avoid GSlot created by altering CFrom in CSlot slot"
  if-finished-working-on-task (lambda (task)
                                (declare (ignore task))
                                (and *not-for-real*
                                     (is-a-kind-of *cur-slot* 'g-slot)
                                     ;; TODO - is c-slot-subs supposed to be dereferenced? are these parameters swapped? is this ever reached?
                                     ;; is it supposed to be '(c-slot-sibs) ? that matches the usage in h-avoid-2-and
                                     (memb (cadr (assoc 'slot-to-change *cur-sup*))
                                           'c-slot-sibs)
                                     (setf *doomed-u* (subset *new-units* (lambda (u)
                                                                            (some 
                                                                             ;; Match a (c-from -> ...) applics shape
                                                                             (lambda (z)
                                                                               (and (eq (cadr z) '->)
                                                                                    (eq (car z) 'c-from)))
                                                                             ;; TODO - unwind/relabel some of this
                                                                             (car (last (find-if (lambda (a)
                                                                                                   (memb u (cadr a)))
                                                                                                 (applics (car (creditors u))))))))))))
  then-print-to-user (lambda (c)
                       (declare (ignore c))
                       (cprin1 14 "~%Hm; I have had bad experiences in the past trying to find " 'g-slot
                               " of units by altering their " 'c-slot
                               " slot, by chaing a " 'c-from " into a " 'c-to
                               ", and this is similar; "
                               "I have just killed these units: "
                               *doomed-u* "~%")
                       (setf *new-units* (set-diff *new-units* *doomed-u*))
                       t)
  then-delete-old-concepts (lambda (c)
                             (declare (ignore c))
                             (mapc #'kill-unit *doomed-u*)
                             t)
  arity 1)

(defheuristic h-avoid-2-and
  isa (heuristic op anything)
  ;; TODO - I wonder if RLL also had template strings where it printed list values into here
  english "IF the current task is to find Generalizations of some unit, then and we did that by altering its IfWorkingOnTaskslot, (or ANY of these slots: (IfPotentiallyRelevant IfTrulyRelevant IfAboutToWorkOnTask IfWorkingOnTask IfFinishedWorkingOnTask)) then make sure we didn't change a AND into anything"
  if-potentially-relevant null
  worth 700
  abbrev "Avoid Generalizations created by altering AND in IfWorkingOnTask slot"
  if-finished-working-on-task (lambda (task)
                                (declare (ignore task))
                                (and *new-units*
                                     (is-a-kind-of *cur-slot* 'generalizations)
                                     (memb (cadr (assoc 'slot-to-change *cur-sup*))
                                           '(if-potentially-relevant
                                             if-truly-relevant
                                             if-about-to-work-on-task
                                             if-working-on-task
                                             if-finished-working-on-task))
                                     (setf *doomed-u* (subset *new-units* (lambda (u)
                                                                            (some (lambda (z)
                                                                                    (and (eq (cadr z) '->)
                                                                                         (eq (car z) 'and)))
                                                                                  (car (last (find-if (lambda (a)
                                                                                                        (memb u (cadr a)))
                                                                                                      (applics (car (creditors u))))))))))))
  then-print-to-user (lambda (c)
                       (declare (ignore c))
                       (cprin1 14 "~%Hm; I have had bad experiences in the past trying to find " 'generalizations
                               " of units by altering their " 'if-working-on-task " slot, by changing a " 'and
                               " into a " 'the-first-of ", and thi sis similar; "
                               "I have just killed these units: " *doomed-u* "~%")
                       (setf *new-units* (set-diff *new-units* *doomed-u*))
                       t)
  then-delete-old-concepts (lambda (c)
                             (declare (ignore c))
                             (mapc #'kill-unit *doomed-u*)
                             t)
  creditors (h13)
  arity 1)

(defheuristic h-avoid-3
  isa (heuristic op anything)
  english "IF the current task is to find GSlot of some unit, then and we did that by altering its CSlot slot, (or ANY of these slots: CSlotSibs) then make sure we didn't change something into a CTo"
  if-potentially-relevant null
  worth 700
  abbrev "Avoid GSlot created by altering something into a CTo in CSlot slot"
  if-finished-working-on-task (lambda (task)
                                (declare (ignore task))
                                (and *not-for-real*
                                     (is-a-kind-of *cur-slot* 'g-slot)
                                     (memb (cadr (assoc 'slot-to-change *cur-sup*))
                                           'c-slot-sibs)
                                     (setf *doomed-u* (subset *new-units*
                                                              (lambda (u)
                                                                (some (lambda (z)
                                                                        (and (eq (cadr z) '->)
                                                                             (eq (caddr z) 'c-to)))
                                                                      (car (last (some (lambda (a)
                                                                                         (memb u (cadr a)))
                                                                                       (applics (car (creditors u))))))))))))
  then-print-to-user (lambda (c)
                       (declare (ignore c))
                       (cprin1 14 "~%Hm; I have had bad experiences in the past trying to find " 'g-slot
                               " of units by altering their " 'c-slot " slot, by changing a " 'c-from " into a " 'c-to
                               ", and this is similar; "
                               "I have just killed these units: " *doomed-u* "~%")
                       (setf *new-units* (set-diff *new-units* *doomed-u*))
                       t)
  then-delete-old-concepts (lambda (c)
                             (declare (ignore c))
                             (mapc #'kill-unit *doomed-u*)
                             t)
  arity 1)

(defheuristic h-avoid-3-first
  isa (heuristic op anything)
  english "IF the current task is to find Generalizations of some unit, then and we did that by altering its IfWorkingOnTask slot, (or ANY of these slots; (IfPotentiallyRelevant IfTrulyRelevant IfAboutToWorkOnTask IfWorkingOnTask IfFinishedWorkingOnTask)) then make sure we didn't change something into a TheFirstOf"
  if-potentially-relevant null
  worth 700
  abbrev "Avoid Generalizations created by altering something into a TheFirstOf in IfWorkingOnTask slot"
  if-finished-working-on-task (lambda (task)
                                (declare (ignore task))
                                (and *new-units*
                                     (is-a-kind-of *cur-slot* 'generalizations)
                                     (memb (cadr (assoc 'slot-to-change *cur-sup*))
                                           '(if-potentially-relevant
                                             if-truly-relevant
                                             if-about-to-work-on-task
                                             if-finished-working-on-task))
                                     (setf *doomed-u* (subset *new-units*
                                                              (lambda (u)
                                                                (some (lambda (z)
                                                                        (and (eq (cadr z) '->)
                                                                             (eq (caddr z) 'the-first-of)))
                                                                      (car (last (some (lambda (a)
                                                                                         (memb u (cadr a)))
                                                                                       (applics (car (creditors u))))))))))))
  then-print-to-user (lambda (c)
                       (declare (ignore c))
                       (cprin1 14 "~%Hm; I have had bad experiences in the past trying to find " 'generalizations
                               " of units by altering their " 'if-working-on-task
                               " slot, by changing a " 'and " into a " 'the-first-of ", and this is similar; "
                               " I have just killed these units: " *doomed-u* "~%")
                       (setf *new-units* (set-diff *new-units* *doomed-u*))
                       t)
  then-delete-old-concepts (lambda (c)
                             (declare (ignore c))
                             (mapc #'kill-unit *doomed-u*)
                             t)
  creditors (h14)
  arity 1)

(defheuristic h-avoid-if-working
  isa (heuristic op anything)
  english "IF the current task is to find Generalizations of some unit, then think twice if the slot to change is IfWorkingOnTask"
  if-potentially-relevant null
  worth 700
  abbrev "Avoid Generalizations created by altering IfWorkingOnTask"
  if-about-to-work-on-task (lambda (task)
                             (declare (ignore task))
                             ;; ORIG: Note the element of chance in whether this advice is followed or not
                             ;; 9 out of 10 chance of being followed
                             (and (is-a-kind-of *cur-slot* 'generalizations)
                                  (eq (cadr (assoc 'slot-to-change *cur-sup*))
                                      'if-working-on-task)
                                  (not (eq 1 (rand 1 10)))))
  then-print-to-user (lambda (task)
                       (cprin1 14 "~%Hm; I have had bad experiences in the past trying to find "
                               'generalizations " of units by altering their "
                               'if-working-on-task " slot, and this is similar; "
                               " I'm just going to abort this entire task!~%")
                       ;; TODO - lose the exclamation mark?
                       (setf *abort-task?* 'abort-task!))
  arity 1)



