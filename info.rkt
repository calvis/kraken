#lang info

(define version "0.0")
(define collection "kraken")
(define test-omit-paths 
  (list "info.rkt" "lang/main.rkt" "main.rkt"))
(define scribblings 
  (list '("doc/kraken.scrbl" ())))
(define deps
  (list "base" "rackunit-lib" "scribble-lib" "racket-doc"))
