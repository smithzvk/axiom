; 05  Separation kernel: information-flow security (noninterference)
;
; Industry context: Rockwell Collins (now Collins Aerospace) used ACL2 to
; prove the partitioning guarantees of the AAMP7G microprocessor's
; separation kernel.  The proof went into the high-assurance evaluation
; that led to NSA certification of the chip for systems handling data at
; several classification levels at once (the MILS architecture).
; Greve, Wilding and Vanfleet's "GWV" formulation of the property
; underlies this file.
;
; The model:
;   * a set of partitions, each with private memory;
;   * application code that is completely arbitrary: it is introduced
;     with ENCAPSULATE as unknown functions, so the theorem holds for
;     every program any partition might run, including malicious ones;
;   * a kernel that schedules one partition per step and delivers
;     messages between partitions only when an information-flow POLICY
;     permits that channel.
;
; The theorem: take any set D of partitions that is closed under the
; policy (nothing outside D may send into D).  If two system states
; agree on D's memories, they still agree on D after any sequence of
; schedule and input events.  So nothing outside D, not its secrets and
; not its behaviour, can affect anything D can observe.
;
; Finally the generic theorem is instantiated, by functional
; instantiation, for a concrete SECRET/UNCLASSIFIED configuration with a
; one-way "data diode".  Each new deployment's policy is checked this way
; without redoing the main proof.

(in-package "ACL2")

;; ---------------------------------------------------------------------
;; System state: an association list from partition name to memory.

(defun get-mem (p st) (cdr (assoc-equal p st)))
(defun put-mem (p m st) (cons (cons p m) st))

(defthm get-mem-put-mem
  (equal (get-mem p (put-mem q m st))
         (if (equal p q) m (get-mem p st))))

(in-theory (disable get-mem put-mem))

;; ---------------------------------------------------------------------
;; Arbitrary application software.  Given a partition's own memory and an
;; external input, a step produces new memory and optionally a message
;; for a destination partition; RECV is how a partition absorbs an
;; incoming message.  Nothing at all is assumed about these functions.

(encapsulate
  (((app-next * *) => *)
   ((app-dst  * *) => *)
   ((app-msg  * *) => *)
   ((app-recv * *) => *))
  (local (defun app-next (mem in) (declare (ignore in)) mem))
  (local (defun app-dst  (mem in) (declare (ignore mem in)) nil))
  (local (defun app-msg  (mem in) (declare (ignore mem in)) nil))
  (local (defun app-recv (mem msg) (declare (ignore msg)) mem)))

;; ---------------------------------------------------------------------
;; The policy ALLOWED(src, dst), and a set D of partitions (given by its
;; membership predicate IN-D) that is closed under incoming flows.

(encapsulate
  (((allowed * *) => *)
   ((in-d *) => *))
  (local (defun allowed (src dst) (declare (ignore src dst)) nil))
  (local (defun in-d (p) (declare (ignore p)) nil))
  (defthm d-closed-under-incoming-flows
    (implies (and (in-d dst) (allowed src dst))
             (in-d src))))

;; ---------------------------------------------------------------------
;; The kernel.  An event is (active-partition . input).

(defun kstep (ev st)
  (let* ((a   (car ev))
         (in  (cdr ev))
         (mem (get-mem a st))
         (st1 (put-mem a (app-next mem in) st))
         (dst (app-dst mem in)))
    (if (and (allowed a dst) (not (equal dst a)))
        (put-mem dst (app-recv (get-mem dst st1) (app-msg mem in)) st1)
      st1)))                            ; message dropped by the kernel

(defun krun (evs st)
  (if (endp evs)
      st
    (krun (cdr evs) (kstep (car evs) st))))

;; ---------------------------------------------------------------------
;; Noninterference

(defun-sk agree-on-d (s1 s2)
  (forall p (implies (in-d p)
                     (equal (get-mem p s1) (get-mem p s2)))))

(defthm kstep-agrees-on-each-d-partition
  ;; One step, one partition p in D.  Cases: p ran (its own memory was
  ;; equal); p received a message (then the sender is in D by closure, so
  ;; the sender's memory, and hence the message, was equal); or p was
  ;; untouched.
  (implies (and (agree-on-d s1 s2) (in-d p))
           (equal (get-mem p (kstep ev s1))
                  (get-mem p (kstep ev s2))))
  :hints (("Goal"
           :in-theory (disable agree-on-d agree-on-d-necc
                               d-closed-under-incoming-flows)
           :use ((:instance agree-on-d-necc)
                 (:instance agree-on-d-necc (p (car ev)))
                 (:instance d-closed-under-incoming-flows
                            (src (car ev)) (dst p))))))

(defthm kstep-preserves-agreement
  (implies (agree-on-d s1 s2)
           (agree-on-d (kstep ev s1) (kstep ev s2)))
  :hints (("Goal" :expand ((agree-on-d (kstep ev s1) (kstep ev s2)))
                  :in-theory (disable kstep agree-on-d))))

(defun krun2-induct (evs s1 s2)        ; induction scheme: run two systems
  (if (endp evs)
      (list s1 s2)
    (krun2-induct (cdr evs) (kstep (car evs) s1) (kstep (car evs) s2))))

(defthm krun-preserves-agreement
  (implies (agree-on-d s1 s2)
           (agree-on-d (krun evs s1) (krun evs s2)))
  :hints (("Goal" :induct (krun2-induct evs s1 s2)
                  :in-theory (disable agree-on-d kstep))))

;; The headline theorem, in the form a certifier reads it.
(defthm noninterference
  (implies (and (agree-on-d s1 s2)
                (in-d p))
           (equal (get-mem p (krun evs s1))
                  (get-mem p (krun evs s2))))
  :hints (("Goal" :in-theory (disable agree-on-d agree-on-d-necc krun)
                  :use ((:instance agree-on-d-necc
                                   (s1 (krun evs s1))
                                   (s2 (krun evs s2)))))))

;; A companion integrity property: a partition that is neither running
;; nor the target of a permitted message is left untouched by a step.
(defthm kstep-isolation
  (implies (and (not (equal p (car ev)))
                (not (and (allowed (car ev) p)
                          (equal p (app-dst (get-mem (car ev) st) (cdr ev))))))
           (equal (get-mem p (kstep ev st))
                  (get-mem p st))))

;; ---------------------------------------------------------------------
;; A concrete deployment: a cross-domain system.  SECRET may receive from
;; UNCLASSIFIED (a one-way diode) and partitions may talk to themselves;
;; nothing flows downward.  We want the unclassified side to be
;; unaffected by anything on the secret side, so D = {UNCLASSIFIED}.

(defun diode-allowed (src dst)
  (or (equal src dst)
      (and (equal src 'unclassified) (equal dst 'secret))))

(defun unclass-only (p) (equal p 'unclassified))

(defun-sk agree-on-unclass (s1 s2)
  (forall p (implies (unclass-only p)
                     (equal (get-mem p s1) (get-mem p s2)))))

(defun kstep-diode (ev st)
  (let* ((a   (car ev))
         (in  (cdr ev))
         (mem (get-mem a st))
         (st1 (put-mem a (app-next mem in) st))
         (dst (app-dst mem in)))
    (if (and (diode-allowed a dst) (not (equal dst a)))
        (put-mem dst (app-recv (get-mem dst st1) (app-msg mem in)) st1)
      st1)))

(defun krun-diode (evs st)
  (if (endp evs)
      st
    (krun-diode (cdr evs) (kstep-diode (car evs) st))))

;; ACL2 checks only the policy obligation (the closure property for
;; this policy and this D, plus the fact that the concrete definitions
;; match the generic ones) and reuses the generic proof.
(defthm diode-noninterference
  (implies (and (agree-on-unclass s1 s2)
                (unclass-only p))
           (equal (get-mem p (krun-diode evs s1))
                  (get-mem p (krun-diode evs s2))))
  :hints (("Goal"
           :by (:functional-instance
                noninterference
                (allowed diode-allowed)
                (in-d unclass-only)
                (agree-on-d agree-on-unclass)
                (agree-on-d-witness agree-on-unclass-witness)
                (kstep kstep-diode)
                (krun krun-diode)))
          ;; the remaining obligation is the choice axiom for the new
          ;; witness function, discharged with the quantifier's NECC lemma
          ("Subgoal 2" :use ((:instance agree-on-unclass-necc
                                        (p 'unclassified)))))
  :rule-classes nil)
