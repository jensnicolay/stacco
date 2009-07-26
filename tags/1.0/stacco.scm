(begin

  ;;helpers
  
  (define (assert-non-empty-list lst msg)
    (if (not (list? lst))
        (display msg)))
  
  (define (make-state stack env reason)
    (vector stack env))
  
  (define (state-stack state)
    (vector-ref state 0))
  
  (define (state-env state)
    (vector-ref state 1))
  
  (define (update-state state stack env)
    (vector-set! state 0 stack)
    (vector-set! state 1 env)
    state)
 
  (define (symbol-prefix name)
    (let*
        ((str (symbol->string name))
         (len (string-length str))
         (fst (if (= 0 len) #f (string->symbol (substring str 0 1)))) 
         (rst (if (= 1 len) #f (string->symbol (substring str 1 (string-length str))))))
      (cons fst rst)))
  
  (define (clone x)
    (cond
      ((pair? x) (cons (car x) (cdr x)))
      ((list? x) (map (lambda (y) y) x))
      ((vector? x) (let* ((len (vector-length x))
                          (newx (make-vector len)))
                     (let loop ((i (- len 1)))
                       (vector-set! newx i (vector-ref x i))
                       (if (> i 0)
                          (loop (- i 1))
                          newx))))
      (else x)))

  (define (bind-identifier name exp env)
     (cons (cons name exp) env))
  
  (define (set-identifier! name exp env)
    (let
        ((binding (assoc name env)))
      (if binding
          (begin
            (set-cdr! binding exp)
            env)  
          (cons (cons name exp) env))))
  
  (define (rappend stack lst)
    (if (null? stack)
       lst
       (rappend (cdr stack) (cons (car stack) lst))))
  
  (define (evaluate-list lst state cont)
    (let
        ((stack (state-stack state)))
    (define (for-each-element lst)
      (if (null? lst)
        (cont (update-state state (cons (reverse (state-stack state)) stack) (state-env state)))
        (let
            ((el (car lst)))
          (cond
            ((list? el) (evaluate-list el state
                                      (lambda (rstate)
                                        (for-each-element (cdr lst)))))
            ((symbol? el) (let
                              ((prefix (symbol-prefix el)))
                            (if (eq? '@ (car prefix))
                               (evaluate (cdr prefix) state
                                        (lambda (rstate)
                                          (for-each-element (cdr lst))))
                               (if (eq? '$ (car prefix))
                                  (cont (update-state state (cons (rappend (state-stack state) lst) stack) (state-env state)))
                                  (begin
                                    (update-state state (cons el (state-stack state)) (state-env state))
                                    (for-each-element (cdr lst)))))))
            (else (update-state state (cons el (state-stack state)) (state-env state))
                 (for-each-element (cdr lst)))))))
      (update-state state '() (state-env state))
      (for-each-element lst)))
  
  (define (evaluate exp state cont)
    (define (default)
      (let*
              ((env (state-env state))
               (lookup (assoc exp env)))
            (if lookup
               (let
                   ((value (cdr lookup)))
                 (if (procedure? value)
                    (value state cont)
                    (let
                        ((stack (state-stack state)))
                      (if (and (symbol? exp) (char<=? (string-ref (symbol->string exp) 0) #\Z) (char>=? (string-ref (symbol->string exp) 0) #\A))
                         (cont (update-state state (cons value stack) env))
                         (state-apply (update-state state (cons value stack) env) cont)))))
               (cont (update-state state (cons exp (state-stack state)) env)))))
    (cond
      ((list? exp) (evaluate-list exp state cont))
      ((symbol? exp) (let ((prefix (symbol-prefix exp)))
                       (if (eq? '$ (car prefix))
                          (evaluate (cdr prefix) state
                                   (lambda (rstate)
                                     (let
                                         ((stack (state-stack rstate)))
                                       (cont (update-state rstate (cons (list '$ (car stack)) (cdr stack)) (state-env rstate))))))
                          (default))))
      (else (default))))
  
  ;; primitives
  
  (define (state-apply state cont)
    (let*
        ((stack (state-stack state))
         (env (state-env state))
         (body (car stack)))
      (set! stack (cdr stack))
      (if (procedure? body)
         (let*
             ((args (car stack))
              (stack2 (cons (apply body args) (cdr stack))))
           (cont (update-state state stack2 env)))
         (letrec
             ((for-each-instruction
               (lambda (instructions state2)
                 (if (null? instructions)
                     (cont (update-state state (state-stack state2) env))
                     (evaluate (car instructions) state2
                               (lambda (rstate)
                                 (for-each-instruction (cdr instructions) rstate)))))))
           (if (null? body)
               (cont (update-state state stack env))
               (begin
                 (if (eq? (car body) '$)
                    (for-each-instruction (cdr body) (make-state stack env (cdr body)))
                    (for-each-instruction body (make-state stack env body)))))))))
  
  (define (state-def state cont)
    (let*
        ((stack (state-stack state))
         (env (state-env state))
         (names (car stack)))
      (set! stack (cdr stack))
      (for-each
       (lambda (name)
         (assert-non-empty-list stack (list "stack underflow while defining" name "in" names))
         (set! env (bind-identifier name (car stack) env))
         (set! stack (cdr stack)))
       (reverse names))
      (cont (update-state state stack env))))
   
  (define (state-and state cont)
    (let*
        ((stack (state-stack state))
         (b (car stack))
         (a (cadr stack)))
      (cont (update-state (cons (and a b)  (cddr stack)) (state-env state)))))  
  
  (define (state-or state cont)
    (let*
        ((stack (state-stack state))
         (b (car stack))
         (a (cadr stack)))
      (cont (update-state state (cons (or a b) (cddr stack)) (state-env state)))))
  
  (define (state-if state cont)
    (let*
        ((stack (state-stack state))
         (alternative (car stack))
         (consequent (cadr stack))
         (predicate (caddr stack)))
      (state-apply (update-state state (cons (if predicate consequent alternative) (cdddr stack)) (state-env state)) cont)))
  
  (define (state-while state cont)
    (let*
        ((stack (state-stack state))
         (condition (car stack))
         (body (cadr stack)))
      (letrec
          ((while-continuation (lambda (state)
                                 (let
                                     ((stack  (state-stack state)))
                                   (state-apply (update-state state (cons condition stack) (state-env state))
                                                (lambda (rstate)
                                                  (let
                                                      ((rstack (state-stack rstate)))
                                                    (if (car rstack)
                                                        (state-apply (update-state rstate (cons body (cdr rstack)) (state-env rstate))
                                                                     while-continuation)
                                                        (cont (update-state rstate (cdr rstack) (state-env rstate)))))))))))
        (while-continuation (update-state state (cddr stack) (state-env state))))))
          
  (define (state-clear state cont)
      (cont (update-state state '() (state-env state))))
  
  (define (state-load state cont)
    (let
        ((stack (state-stack state)))
      (cont (update-state state (call-with-input-file (car stack) (lambda (port)
                                                                    (let loop ((stack (cdr stack)))
                                                                      (let
                                                                          ((exp (read port)))
                                                                        (if (eof-object? exp)
                                                                            stack
                                                                            (loop (cons exp stack))))))) (state-env state)))))
  
  (define (state-capture state cont)
    (cont (update-state state (cons state (state-stack state)) (state-env state))))
  
  (define (state-clone state cont)
    (let
        ((stack (state-stack state)))
      (cont (update-state state (cons (clone (car stack)) (cdr stack)) (state-env state)))))
  
  (define (state-become state cont)
    (let*
        ((stack (state-stack state))
         (become (car stack)))
      (update-state state (cdr stack) (state-env state)) ; important since state=become possible
      (cont become)))
  
  (define (state-native state cont)
    (let*
        ((stack (state-stack state))
         (name (caar stack))
         (binding (eval name (interaction-environment))))
      (cont (update-state state (cons binding (cdr stack)) (state-env state)))))

  (define (state-send state cont)
    (let*
        ((stack (state-stack state))
         (message (car stack))
         (receiver (cadr stack))
         (send-continuation
          (lambda (rstate)
            (cont state))))
      (update-state state (cddr stack) (state-env state)) ; important since receiver=state is possible
      (state-apply (update-state receiver (cons message (state-stack receiver)) (state-env receiver)) send-continuation)))
  
  ;; global
  
  (define global-env '())
  
  (define (globalize identifier value)
    (set! global-env (bind-identifier identifier value global-env)))
  
  (globalize 'apply state-apply)
  (globalize 'def state-def)
  (globalize 'and state-and)
  (globalize 'or state-or)
  (globalize 'if state-if)
  (globalize 'while state-while)
  (globalize 'clear state-clear)
  (globalize 'capture state-capture)
  (globalize 'become state-become)
  (globalize 'clone state-clone)
  (globalize 'load state-load)
  (globalize 'native state-native)
  (globalize 'send state-send)
  
  (define (rep state)
      (newline)
      (display (reverse (state-stack state)))
      (newline)
      (display "stacco>")
      (evaluate (read) state rep))
  
  
  (state-apply (make-state (cons '("stacco-bootstrap.stc" load apply) '()) global-env 'global)
              (lambda (rstate)
                (rep (update-state rstate (cdr (state-stack rstate)) (state-env (car (state-stack rstate))))))) 
  
  ;(rep (make-state '() global-env 'global))
  )