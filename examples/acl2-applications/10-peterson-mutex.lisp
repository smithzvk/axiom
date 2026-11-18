; 10  Concurrency: mutual exclusion for Peterson's algorithm under every
;     interleaving, and a mechanically found bug in a "harmless" reordering
;
; Industry context: concurrency bugs show up only under rare schedules,
; which is why testing misses them and proof does not.  ACL2 has been
; used for cache-coherence and memory-system verification at Centaur and
; elsewhere, for the JVM's thread semantics, and for distributed
; protocols.  Lock-free algorithms, interrupt handlers sharing data and
; multi-core boot code all raise the same kind of question.
;
; Peterson's algorithm, for processes 0 and 1 (i is me, j the other):
;
;     loop:  0: flag[i] := true
;            1: turn    := j
;            2: await (!flag[j] || turn == i)
;            3: -- critical section --; flag[i] := false; goto 0
;
; Each step executes one labelled statement of the process the scheduler
; picks.  The scheduler is an arbitrary list, so the theorem covers every
; possible interleaving of every length: infinitely many executions.
;
; Proved: no reachable state has both processes in the critical section.
; The method is an inductive invariant, found by hand and checked by
; ACL2.  The book also shows that swapping lines 0 and 1, which looks
; harmless, breaks mutual exclusion, and gives a concrete schedule that
; triggers the bug.

(in-package "ACL2")

;; State: (pc0 pc1 flag0 flag1 turn)
(defun mk (pc0 pc1 f0 f1 turn) (list pc0 pc1 f0 f1 turn))
(defun pc-of (i s) (if (equal i 1) (nth 1 s) (nth 0 s)))
(defun flag (i s) (if (equal i 1) (nth 3 s) (nth 2 s)))
(defun turn (s)   (nth 4 s))
(defun other (i)  (if (equal i 1) 0 1))
(defun pid (x)    (if (equal x 1) 1 0))   ; the scheduler may say anything

(defun upd (i newpc newflag newturn s)  ; update process i's pc and flag
  (if (equal i 1)
      (mk (pc-of 0 s) newpc (flag 0 s) newflag newturn)
    (mk newpc (pc-of 1 s) newflag (flag 1 s) newturn)))

(defun pstep (i s)                      ; process i executes one statement
  (let ((j (other i)))
    (case (pc-of i s)
      (0 (upd i 1 t (turn s) s))
      (1 (upd i 2 (flag i s) j s))
      (2 (if (or (not (flag j s)) (equal (turn s) i))
             (upd i 3 (flag i s) (turn s) s)          ; enter critical section
           s))                                        ; keep waiting
      (otherwise (upd i 0 nil (turn s) s)))))         ; leave, drop flag

(defun run-sched (sched s)
  (if (atom sched)
      s
    (run-sched (cdr sched) (pstep (pid (car sched)) s))))

(defconst *start* (mk 0 0 nil nil 0))

(defun mutex (s) (not (and (equal (pc-of 0 s) 3) (equal (pc-of 1 s) 3))))

;; ---------------------------------------------------------------------
;; The inductive invariant
;;   * pcs are in 0..3 and turn is 0 or 1;
;;   * flag[i] is true exactly when process i is past line 0;
;;   * if i is in the critical section, then j is at line 0 or 1 or it
;;     is i's turn.
;; The last clause is the heart of Peterson's argument: two processes in
;; the critical section would need turn = 0 and turn = 1 at once.

(defun pc-ok (x) (member x '(0 1 2 3)))

(defun inv-for (i s)
  (let ((j (other i)))
    (and (pc-ok (pc-of i s))
         (iff (flag i s) (not (equal (pc-of i s) 0)))
         (implies (equal (pc-of i s) 3)
                  (or (equal (pc-of j s) 0)
                      (equal (pc-of j s) 1)
                      (equal (turn s) i))))))

(defun inv (s)
  (and (or (equal (turn s) 0) (equal (turn s) 1))
       (inv-for 0 s)
       (inv-for 1 s)))

(defthm inv-start (inv *start*))

(defthm inv-implies-mutex
  (implies (inv s) (mutex s)))

(defthm pstep-preserves-inv
  (implies (inv s) (inv (pstep i s))))

(in-theory (disable inv pstep mutex))

(defthm run-preserves-inv
  (implies (inv s) (inv (run-sched sched s))))

;; Headline theorem: every schedule from the start state keeps mutual
;; exclusion.
(defthm peterson-mutual-exclusion
  (mutex (run-sched sched *start*)))

;; ---------------------------------------------------------------------
;; The "harmless" reordering: set turn first, then raise the flag.

(defun pstep-bad (i s)
  (let ((j (other i)))
    (case (pc-of i s)
      (0 (upd i 1 (flag i s) j s))                    ; turn := j first
      (1 (upd i 2 t (turn s) s))                      ; then flag := true
      (2 (if (or (not (flag j s)) (equal (turn s) i))
             (upd i 3 (flag i s) (turn s) s)
           s))
      (otherwise (upd i 0 nil (turn s) s)))))

(defun run-bad (sched s)
  (if (atom sched)
      s
    (run-bad (cdr sched) (pstep-bad (pid (car sched)) s))))

;; The counterexample schedule:
;;   P0 sets turn:=1.  P1 sets turn:=0, raises its flag and, seeing
;;   flag0 still false, enters.  P0 raises its flag and, seeing turn=0,
;;   enters as well.
(defthm reordered-peterson-is-broken
  (not (mutex (run-bad '(0 1 1 1 0 0) *start*)))
  :hints (("Goal" :in-theory (enable mutex)))
  :rule-classes nil)
