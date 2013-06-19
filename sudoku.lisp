;;;
;;; Simple and naive sudoku solver, using simple constraint propagation, and depth first search
;;;

(defpackage :simple-sudoku-solver
  (:use :common-lisp))

(in-package :simple-sudoku-solver)

;;; Sudoku:
;;;   A board contains 3x3 large squares, each large square contains 3x3 small squares, so a board has totally 9x9 small squares
;;;   Initially some small squares are filled with 1 to 9, and the rest are empty.
;;;   The goal is to fill in the empty small squares with 1 to 9, such that
;;;     1. each row contains a permutation of 1, 2, ..., 9
;;;     2. each column contains a permutation of 1, 2, ..., 9
;;;     3. each large square contains a permutation of 1, 2, ..., 9

;;; a small set containing 1 to 9 is useful here, a small set is represented as an integer, where each bit indicate the presence of one of 1 to 9
(defun empty-set? (s) (= s 0))
(defun singleton (n) (ash 1 n))
(defun intersect-set (s1 s2) (logand s1 s2))
(defun union-set (s1 s2) (logior s1 s2))
(defparameter *universal-set* #b1111111110)
(defun complement-set (s) (logand *universal-set* (lognot s)))
(defun difference-set (s1 s2) (intersect-set s1 (complement-set s2)))
(defparameter *singletons*
  (let ((s (make-array 10 :initial-element nil)))
    (dotimes (i 9 s)
      (setf (aref s (1+ i)) (singleton (1+ i))))))
(defun singleton? (s) (find s *singletons*))
(defun singleton-num (s) (position s *singletons*))

;;; a board is (internally) represented as a 9x9 2D array of small sets
(defun empty-board ()
  (make-array '(9 9) :initial-element *universal-set*))
(defun copy-board (b)
  (let ((nb (empty-board)))
    (dotimes (i 9)
      (dotimes (j 9)
	(setf (aref nb i j) (aref b i j))))
    nb))
(defun list-to-board (ns)
  ;; ns is a list of 0-9 which is the initial content of the board arranged in row by row, where 0 represents empty small square.
  ;; returns a board for this initial configuration
  (let ((b (empty-board)))
    (dotimes (i 9)
      (dotimes (j 9)
	(let ((n (pop ns)))
	  (setf (aref b i j) (if (= n 0) *universal-set* (singleton n))))))
    b))

(defun print-raw-board (b)
  (let ((sep1 "+---+---+---+")
	(sep2 "+===+===+===+"))
    (labels ((pr-sep (sp)
	       (dotimes (i 3) (format t "~a" sp))
	       (terpri))
	     (pr-cell (n) (format t "| ~a " (if n n #\space)))
	     (pr-row (i)
	       (dotimes (j 9)
		 (pr-cell (singleton-num (aref b i j)))
		 (if (or (= j 2) (= j 5)) (format t "|")))
	       (format t "|~%")))
      ;;
      (dotimes (i 9)
	(pr-sep (if (= 0 (mod i 3)) sep2 sep1))
	(pr-row i))
      (pr-sep sep2))))

(defun print-board (b)
  (if b (print-raw-board b) (format t "Invalid Board!~%")))
;;
(defun valid-board (b)
  ;; returns two values: is-valid and is-complete
  (let ((is-complete t))
    (dotimes (i 9)
      (dotimes (j 9)
	(
;;
(defparameter *test*
  '(0 0 0  3 0 5  0 6 0
    3 0 7  6 0 4  0 0 0
    0 8 0  0 0 9  3 0 4

    9 0 0  1 3 0  0 0 8
    0 6 4  0 2 0  9 7 0
    8 0 0  0 4 7  0 0 1

    2 0 5  8 0 0  0 9 0
    0 0 0  7 0 3  2 0 5
    0 9 0  4 0 2  0 0 0))
(defparameter *test-b* (list-to-board *test*))
;; (print-board *test-b*)
; +===+===+===++===+===+===++===+===+===+
; |   |   |   || 3 |   | 5 ||   | 6 |   |
; +---+---+---++---+---+---++---+---+---+
; | 3 |   | 7 || 6 |   | 4 ||   |   |   |
; +---+---+---++---+---+---++---+---+---+
; |   | 8 |   ||   |   | 9 || 3 |   | 4 |
; +===+===+===++===+===+===++===+===+===+
; | 9 |   |   || 1 | 3 |   ||   |   | 8 |
; +---+---+---++---+---+---++---+---+---+
; |   | 6 | 4 ||   | 2 |   || 9 | 7 |   |
; +---+---+---++---+---+---++---+---+---+
; | 8 |   |   ||   | 4 | 7 ||   |   | 1 |
; +===+===+===++===+===+===++===+===+===+
; | 2 |   | 5 || 8 |   |   ||   | 9 |   |
; +---+---+---++---+---+---++---+---+---+
; |   |   |   || 7 |   | 3 || 2 |   | 5 |
; +---+---+---++---+---+---++---+---+---+
; |   | 9 |   || 4 |   | 2 ||   |   |   |
; +===+===+===++===+===+===++===+===+===+

;;; Constraint propagation
(defun propagate-constraints (nb cells-to-do)
  (labels ((limit-cell-at (x y choice-to-remove)
	     (let ((old (aref nb x y)))
	       (if (singleton? old)
		   (if (= old choice-to-remove) (return-from propagate-constraints nil))
		   (if (singleton? (setf (aref nb x y) (difference-set old choice-to-remove)))
		       (push (cons x y) cells-to-do)))))
	   (propagate-at (x y)
	     ;; cell are (x,y) is already singleton, propagate it
	     (let ((w (aref nb x y))
		   (sq-x (- x (mod x 3)))
		   (sq-y (- y (mod y 3))))
	       (dotimes (i 9) (if (/= i x) (limit-cell-at i y w))) ; row
	       (dotimes (j 9) (if (/= j y) (limit-cell-at x j w))) ; column
	       (dotimes (i 3) ; large square
		 (dotimes (j 3)
		   (if (or (/= (+ sq-x i) x) (/= (+ sq-y j) y))
		       (limit-cell-at (+ sq-x i) (+ sq-y j) w)))))))
      ;;
      (loop while cells-to-do
	 do (let ((cell (pop cells-to-do)))
	      (propagate-at (car cell) (cdr cell)))
	 finally (return nb))))

(defun put-on-board (b i j s)
  ;; assuming the board b is valid
  ;; put the singleton s on the (i,j)th cell of board b, propagate the constraints, and return a new board if ok.
  ;; returns nil if constraints violated.
  (let ((nb (copy-board b)))
    (setf (aref nb i j) s)
    (propagate-constraints nb (list (cons i j)))))

;;
(defun init-propagate-board (b)
  ;; propagate the constraints of the singleton positions of b
  (let ((cells-to-do nil))
    (dotimes (i 9)
      (dotimes (j 9)
	(if (singleton? (aref b i j))
	    (push (cons i j) cells-to-do))))
    (propagate-constraints b cells-to-do)))
;;
(defparameter *test-b-p* (init-propagate-board (copy-board *test-b*)))