use
    order_relation
end


A: ANY


is_complete_semilattice (r:{A,A}): ghost BOOLEAN
    -> r.is_partial_order
       and
       all(p) p <= r.carrier ==> p.has_infimum(r)



is_complete_lattice (r:{A,A}): ghost BOOLEAN
    -> r.is_partial_order
       and
       (all(p) p <= r.carrier ==> p.has_infimum(r))
       and
       (all(p) p <= r.carrier ==> p.has_supremum(r))



all(r:{A,A})
        -- Every complete semilattice is also a complete lattice.
    require
        r.is_complete_semilattice
    ensure
        r.is_complete_lattice
    assert
        all(p)
            require
                p <= r.carrier
            ensure
                p.has_supremum(r)
            assert
                p.upper_bounds(r).has_infimum(r)
            via
                some(x) x.is_infimum(p.upper_bounds(r), r)
                assert
                    x.is_supremum(p,r)
            end
    end

