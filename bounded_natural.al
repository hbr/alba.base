use
    core
end


{:
Basic Definitions
=================
:}

deferred class N:BOUNDED_NATURAL

0: N               deferred end
bit_size: N        deferred end

successor  (a:N): N  deferred end
predecessor(a:N): N  deferred end

greatest:N  = 0.predecessor

1: N    = 0.successor
2: N    = 1.successor
3: N    = 2.successor
4: N    = 3.successor
5: N    = 4.successor
6: N    = 5.successor
7: N    = 6.successor
8: N    = 7.successor
9: N    = 8.successor
hex_a:N = 9.successor
hex_b:N = hex_a.successor
hex_c:N = hex_b.successor
hex_d:N = hex_c.successor
hex_e:N = hex_d.successor
hex_f:N = hex_e.successor

ten: N  = 9.successor
hex: N  = hex_f.successor


all(a:N, p:{N})
        -- Axioms Part 1
    ensure
        a.successor.predecessor = a
        a = greatest ==> a.successor = 0
        a = a.successor ==> false

        0 in p
        ==>
        (all(n) n /= greatest ==> n in p ==> n.successor in p)
        ==>
        a in p
    deferred
    end


all(a:N)
    require
        a = 0
    ensure
        a /= greatest
    assert
        greatest:N /= greatest.successor
        greatest:N /= 0
    end


all(a:N)
        -- The equality of a number with its successor leads to contradiction.
    require
        a = a.successor
    ensure
        false
    assert
        a /= a.successor
    end


all(a,b:N)
        -- Injectivity of the successor function
    require
        a.successor = b.successor
    ensure
        a = b
    via [ a
        , a.successor.predecessor
        , b.successor.predecessor
        , b
        ]
    end


all(a:N)
        -- Each number is the successor of another number.
    ensure

        some(b) a = b.successor

    inspect
        a
    case 0
        assert
            0:N = greatest.successor
    case b.successor
        assert
            b.successor = b.successor
    end



all(a:N)
        -- Recognizer rule for the constructor 'successor'.
    ensure

        (a /= 0) = (some(b) b /= greatest and a = b.successor)

    assert
        require
            some(b) b /= greatest and a = b.successor
        ensure
            a /= 0
        via
            some(b) b /= greatest and a = b.successor
        end

        require
            a /= 0
        ensure
            some(b) b /= greatest and a = b.successor
        via
            some(b) a = b.successor
        assert
            b /= greatest and a = b.successor
        end
    end



all(a:N)
        -- Recognizers are mutually exclusive.
    ensure
        a = 0  ==> (a /= 0) ==> false
    end



(+) (a,b:N): N
    -> inspect b
       case 0 then
           a
       case n.successor then
           (a + n).successor

(*) (a,b:N): N
    -> inspect b
       case 0 then
           0
       case n.successor then
           (a * n) + a

shift_left (a,b:N): N
    -> inspect
           b
       case 0 then
           a
       case n.successor then
           a.shift_left(n) * 2


all(a:N)
        -- Axioms Part 2
    ensure
        a = bit_size ==> 1.shift_left(a) = 0
    deferred
    end




{:
Successor and Predecessor
=========================
:}

all(a:N)
    require
        a /= greatest
    ensure
        a.successor /= 0
    end


all(a:N)
    ensure
        a.predecessor.successor = a
    inspect
        a
    end




{:
Order Structure
===============
:}

(<=) (a,b:N): BOOLEAN
    -> inspect
           a,b
       case 0, _ then
           true
       case _, 0 then
           false
       case n.successor, m.successor then
           n <= m

(<)  (a,b:N): BOOLEAN
    -> a <= b and a /= b


least_bounded (p:{N}, a:N): N
        -- The least number less or equal 'a' which satisfies 'p' or '0' if
        -- no such number exists.
    -> inspect
           a
       case 0 then
           0
       case n.successor then
           if p.least_bounded(n) = 0 and n.successor in p then
               n.successor
           else
               n



all(a:N)
    ensure
        a <= a
    inspect
        a
    end


{:
Order Structure and 0
---------------------
:}
all(a:N)
    ensure
        0 <= a
    inspect
        a
    end


all(a:N)
    require
        a <= 0
    ensure
        a = 0
    inspect
        a
    end

all(a:N)
    require
        a < 0
    ensure
        false
    end


{:
Order Structure and successor
-----------------------------
:}
all(a,b:N)
    require
        a <= b
        b /= greatest
    ensure
        a < b.successor
    inspect
        a
    case 0
        -- goal: 0 < b.successor
        assert
            b.successor /= 0  -- because 'b /= greatest'
    case n.successor
        {: ind hypo: all(b) n <= b ==> b /= greatest ==> n < b.successor
        :}
        inspect
            b
        case m.successor
            -- goal:     n.successor < m.successor.successor
            assert
                n < m.successor
    end


all(a,b:N)
    require
        a < b.successor
        b /= greatest
    ensure
        a <= b
    inspect
        a
    case n.successor
        inspect
            b
        case 0
            assert
                n.successor < 0.successor
                n < 0   -- contradiction
    end


all(a,b:N)
    require
         a /= greatest
         a.successor <= b
    ensure
         a < b
    inspect
         b
    end


{:
Antisymmetry
------------
:}
all(a,b:N)
    require
        a <= b
        b <= a
    ensure
        a = b
    inspect
        a
    case n.successor
        assert
            all(b) n <= b ==> b <= n ==> n = b  -- ind hypo
        inspect
            b
        case m.successor
            assert
                n = m
    end

{:
Transitivity
------------
:}
all(a,b,c:N)
    require
        a <= b
        b <= c
    ensure
        a <= c
    inspect
        a
    case n.successor
        inspect
             b
        case m.successor
            inspect
                c
            case k.successor
    end


{:
Dichotomy
---------
:}

all(a,b:N)
    ensure
        a <= b or b <= a
    inspect
        a
    case n.successor
        -- ind hypo: all(b) n <= b or b <= n
        inspect
            b
        case m.successor
            if n <= m
            orif m <= n
    end



{:
Wellfounded Relation
====================
:}


all(a:N, p:{N})
    require
        all(a) (all(b) b < a ==> b in p) ==> a in p
    ensure
        a in p
    assert
        all(x)
            require
                 x <= a
            ensure
                 x in p
            inspect
                 a
            case 0
                assert
                    all(b)
                        require
                            b < 0  -- contradiction
                        ensure
                            b in p
                        end
            end
    end




{:
Arithmetic
==========
:}


all(a:N)
    ensure
        0 + a = a
    inspect
        a
    end


all(a,b:N)
    ensure
        (a + b).successor = a.successor + b
    inspect
        b
    case 0
        assert
            0:N /= greatest
    case n.successor
    end

all(a,b:N)
    ensure
        a + b = b + a
    inspect
        b
    case n.successor
        via [ a + n.successor
            , (a + n).successor   -- def '+'
            , (n + a).successor   -- ind hypo
            , n.successor + a     -- previous lemma
            ]
    end


all(a:N)
    ensure
        (greatest + a).successor = a
    inspect
        a
    end

all(a,b:N)
    ensure
        (a + b).successor = a + b.successor
    if b = greatest
        assert
            0:N = greatest.successor
        via [ (a + greatest).successor
            , (greatest + a).successor
            , a
            , a + 0
            , a + greatest.successor
            ]
    orif b /= greatest
    end


all(a,b,c:N)
    ensure
        a + b + c = a + (b + c)
    inspect
        c
    end

complement(a:N): N
        -- The complement of the number 'a' with respect to the greatest element.
        -- 0.complement = greatest, 1.complement = greatest - 1, ...
    -> inspect
           a
       case 0 then
           greatest
       case n.successor then
           n.complement.predecessor



(-) (a,b:N): N
        -- The difference between 'a' and 'b'.
    -> a + b.complement + 1


(/) (a,b:N): N
        -- 'a' divided by 'b'.
    require
        b /= 0
    ensure
        -> {x: x * b <= a and a - x * b < b}.least_bounded(a)
    end


(mod) (a,b:N): N
        -- 'a' modulo 'b'.
    require
        b /= 0
    ensure
        -> a - a/b
    end
