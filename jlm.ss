;;;; jlm: A very simple JVM implemented in Scheme.
;;;; Copyright (C) 2024  CToID <funk443@yandex.com>
;;;;
;;;; This program is free software: you can redistribute it and/or
;;;; modify it under the terms of the GNU General Public License as
;;;; published by the Free Software Foundation, either version 3 of
;;;; the License, or (at your option) any later version.
;;;;
;;;; This program is distributed in the hope that it will be useful,
;;;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;;;; General Public License for more details.
;;;;
;;;; You should have received a copy of the GNU General Public License
;;;; along with this program.  If not, see
;;;; <https://www.gnu.org/licenses/>.

(import (scheme))

(define constant-pool-tags
  '((1 . utf8)
    (3 . integer)
    (4 . float)
    (5 . long)
    (6 . double)
    (7 . class)
    (8 . string)
    (9 . field-ref)
    (10 . method-ref)
    (11 . interface-method-ref)
    (12 . name-and-type)
    (15 . method-handle)
    (16 . method-type)
    (17 . dynamic)
    (18 . invoke-dynamic)
    (19 . module)
    (20 . package)))

(define class-access-flags
  '((#x0001 . public)
    (#x0010 . final)
    (#x0020 . super)
    (#x0200 . interface)
    (#x0400 . abstract)
    (#x1000 . synthetic)
    (#x2000 . annotation)
    (#x4000 . enum)
    (#x8000 . module)))

(define method-access-flags
  '((#x0001 . public)
    (#x0002 . private)
    (#x0004 . protected)
    (#x0008 . static)
    (#x0010 . final)
    (#x0020 . synchronized)
    (#x0040 . bridge)
    (#x0080 . varargs)
    (#x0100 . native)
    (#x0400 . abstract)
    (#x0800 . strict)))

(define-syntax alist-set!
  (syntax-rules ()
    ((_ alist key value)
     (cond
      ((assq 'key alist)
       => (lambda (entry) (set-cdr! entry value)))
      (else
       (set! alist (cons (cons 'key value) alist)))))))

(define-syntax alist-get
  (syntax-rules ()
    ((_ alist key)
     (cdr (assq 'key alist)))))

(define (read-uint port n)
  (let loop ((result 0)
             (i 0))
    (cond
     ((>= i n)
      result)
     (else
      (loop (+ (ash result 8) (get-u8 port))
            (add1 i))))))

(define (read-utf8 port n)
  (utf8->string (get-bytevector-n port n)))

(define (read-constant-pool port constant-pool-tags)
  (define (read-cp-info)
    (define cp-info '())
    (define tag (read-uint port 1))
    (alist-set! cp-info tag (cdr (assv tag constant-pool-tags)))
    (cond
     ((= tag 1)
      (alist-set! cp-info bytes (read-utf8 port (read-uint port 2))))
     ((= tag 7)
      (alist-set! cp-info name-index (read-uint port 2)))
     ((= tag 8)
      (alist-set! cp-info string-index (read-uint port 2)))
     ((or (= tag 9) (= tag 10))
      (alist-set! cp-info class-index (read-uint port 2))
      (alist-set! cp-info name-and-type-index (read-uint port 2)))
     ((= tag 12)
      (alist-set! cp-info name-index (read-uint port 2))
      (alist-set! cp-info descriptor-index (read-uint port 2)))
     (else
      (errorf 'read-cp-info "Tag: ~d" tag)))
    (reverse cp-info))
  (let loop ((cp-count (read-uint port 2))
             (constant-pool '()))
    (cond
     ((<= cp-count 1)
      (reverse constant-pool))
     (else
      (loop (sub1 cp-count)
            (cons (read-cp-info) constant-pool))))))

(define (read-access-flags port flags)
  (define mask (read-uint port 2))
  (let loop ((flags flags)
             (result '()))
    (cond
     ((null? flags)
      (reverse result))
     ((zero? (bitwise-and mask (caar flags)))
      (loop (cdr flags) result))
     (else
      (loop (cdr flags) (cons (cdar flags) result))))))

(define (read-attributes port constant-pool)
  (define (read-attribute-info)
    (define attribute-info '())
    (define name
      (alist-get (list-ref constant-pool
                           (sub1 (read-uint port 2)))
                 bytes))
    (define len (read-uint port 4))
    (alist-set! attribute-info name name)
    (cond
     ((string=? name "Code")
      (alist-set! attribute-info max-stack (read-uint port 2))
      (alist-set! attribute-info max-locals (read-uint port 2))
      (alist-set! attribute-info
                  code
                  (bytevector->u8-list
                   (get-bytevector-n port (read-uint port 4))))
      (unless (zero? (read-uint port 2))
        (errorf 'read-attribute-info
                "Reading exception table is not implemented."))
      (alist-set! attribute-info
                  attributes
                  (read-attributes port constant-pool)))
     ((string=? name "LineNumberTable")
      (alist-set! attribute-info
                  line-number-table
                  (let loop
                      ((line-number-table-length (read-uint port 2))
                       (line-number-table '()))
                    (cond
                     ((<= line-number-table-length 0)
                      (reverse line-number-table))
                     (else
                      (loop (sub1 line-number-table-length)
                            (cons (list (read-uint port 2)
                                        (read-uint port 2))
                                  line-number-table)))))))
     ((string=? name "SourceFile")
      (alist-set! attribute-info sourcefile-index (read-uint port 2)))
     (else
      (alist-set! attribute-info
                  info
                  (get-bytevector-n port len))))
    (reverse attribute-info))
  (let loop ((attributes-count (read-uint port 2))
             (attributes '()))
    (cond
     ((<= attributes-count 0)
      (reverse attributes))
     (else
      (loop (sub1 attributes-count)
            (cons (read-attribute-info) attributes))))))

(define (read-interfaces port)
  (unless (zero? (read-uint port 2))
    (errorf 'read-interfaces
            "Reading interfaces is not implemented."))
  '())

(define (read-fields port)
  (unless (zero? (read-uint port 2))
    (errorf 'read-fields
            "Reading fields is not implemented."))
  '())

(define (read-methods port access-flags constant-pool)
  (define (read-method-info)
    (define method-info '())
    (alist-set! method-info
                access-flags
                (read-access-flags port access-flags))
    (alist-set! method-info name-index (read-uint port 2))
    (alist-set! method-info descriptor-index (read-uint port 2))
    (alist-set! method-info
                attributes
                (read-attributes port constant-pool))
    (reverse method-info))
  (let loop ((methods-count (read-uint port 2))
             (methods '()))
    (cond
     ((<= methods-count 0)
      (reverse methods))
     (else
      (loop (sub1 methods-count)
            (cons (read-method-info) methods))))))

(define (read-class port)
  (define class '())
  (alist-set! class magic (read-uint port 4))
  (alist-set! class minor-version (read-uint port 2))
  (alist-set! class major-version (read-uint port 2))
  (alist-set! class
              constant-pool
              (read-constant-pool port constant-pool-tags))
  (alist-set! class
              access-flags
              (read-access-flags port class-access-flags))
  (alist-set! class this-class (read-uint port 2))
  (alist-set! class super-class (read-uint port 2))
  (alist-set! class interfaces (read-interfaces port))
  (alist-set! class fields (read-fields port))
  (alist-set! class
              methods
              (read-methods port
                            method-access-flags
                            (alist-get class constant-pool)))
  (alist-set! class
              attributes
              (read-attributes port (alist-get class constant-pool)))
  (reverse class))

(define (run-code code constant-pool)
  (let loop ((code code)
             (stack '()))
    (cond
     ((or (null? code) (= (car code) 177))
      (void))
     ((= (car code) 178)
      (let ()
        (define field-index
          (sub1 (bitwise-ior (ash (cadr code) 8) (caddr code))))
        (define field-ref
          (list-ref constant-pool field-index))
        (define class-index
          (sub1 (alist-get field-ref class-index)))
        (define name-and-type-index
          (sub1 (alist-get field-ref name-and-type-index)))
        (define class
          (list-ref constant-pool class-index))
        (define name-and-type
          (list-ref constant-pool name-and-type-index))
        (define class-name-index
          (sub1 (alist-get class name-index)))
        (define field-name-index
          (sub1 (alist-get name-and-type name-index)))
        (define field-descriptor-index
          (sub1 (alist-get name-and-type descriptor-index)))
        (define class-name
          (alist-get (list-ref constant-pool class-name-index)
                     bytes))
        (define field-name
          (alist-get (list-ref constant-pool field-name-index)
                     bytes))
        (define field-descriptor
          (alist-get (list-ref constant-pool field-descriptor-index)
                     bytes))
        (cond
         ((and (string=? class-name "java/lang/System")
               (string=? field-name "out")
               (string=? field-descriptor "Ljava/io/PrintStream;"))
          (loop (list-tail code 3)
                (cons (standard-output-port
                       'line
                       (make-transcoder (utf-8-codec)))
                      stack)))
         (else
          (errorf 'run-code
                  "Unknown class name, field name or field descriptor: ~s, ~s, ~s."
                  class-name
                  field-name
                  field-descriptor)))))
     ((= (car code) 18)
      (let ()
        (define constant-index (sub1 (cadr code)))
        (define constant (list-ref constant-pool constant-index))
        (define constant-type (alist-get constant tag))
        (cond
         ((eq? constant-type 'string)
          (let ()
            (define string-index
              (sub1 (alist-get constant string-index)))
            (define string
              (list-ref constant-pool string-index))
            (define string-content
              (alist-get string bytes))
            (loop (list-tail code 2)
                  (cons string-content stack))))
         (else
          (errorf 'run-code
                  "Constant data ~s is not implemented"
                  constant-type)))))
     ((= (car code) 182)
      (let ()
        (define method-index
          (sub1 (bitwise-ior (ash (cadr code) 8)
                             (caddr code))))
        (define method-ref
          (list-ref constant-pool method-index))
        (define class-index
          (sub1 (alist-get method-ref class-index)))
        (define name-and-type-index
          (sub1 (alist-get method-ref name-and-type-index)))
        (define class
          (list-ref constant-pool class-index))
        (define name-and-type
          (list-ref constant-pool name-and-type-index))
        (define class-name-index
          (sub1 (alist-get class name-index)))
        (define method-name-index
          (sub1 (alist-get name-and-type name-index)))
        (define method-descriptor-index
          (sub1 (alist-get name-and-type descriptor-index)))
        (define class-name
          (alist-get (list-ref constant-pool class-name-index)
                     bytes))
        (define method-name
          (alist-get (list-ref constant-pool method-name-index)
                     bytes))
        (define method-descriptor
          (alist-get (list-ref constant-pool method-descriptor-index)
                     bytes))
        (cond
         ((and (string=? class-name "java/io/PrintStream")
               (string=? method-name "println"))
          (let ()
            (define content (car stack))
            (define port (cadr stack))
            (fprintf port "~a~%" content)
            (loop (list-tail code 3)
                  (list-tail stack 2))))
         (else
          (errorf 'run-code
                  "Unknown method: ~s, ~s, ~s"
                  class-name
                  method-name
                  method-descriptor)))))
     ((= (car code) 17)
      (let ()
        (define byte1 (cadr code))
        (define byte2 (caddr code))
        (define temp
          (+ (ash byte1 8) byte2))
        (define value
          (if (<= temp 32767)
              temp
              (- (- #xffff temp -1))))
        (loop (list-tail code 3)
              (cons value stack))))
     (else
      (errorf 'run-code
              "Bytecode ~d is not implemented."
              (car code))))))

(when (< (length (command-line)) 2)
  (printf "Usage: scheme --program jlm.ss <class-file-path>~%")
  (exit 1))

(define class
  (call-with-port (open-file-input-port (cadr (command-line)))
    read-class))

(define main-method (cadr (alist-get class methods)))
(define code
  (alist-get (car (alist-get main-method attributes)) code))

;; (pretty-print class)
(run-code code (alist-get class constant-pool))

(exit 0)
