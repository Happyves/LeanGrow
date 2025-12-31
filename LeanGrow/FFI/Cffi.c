
// #include <lean/lean.h>
#include "lean.h" // dev

#include <string.h>
// // required by memcpy


/* UInt32Array */

/* Basic */

lean_obj_res lean_copy_sarray_mirror (lean_obj_arg a, size_t cap) {
    unsigned esz   = lean_sarray_elem_size(a);
    size_t sz      = lean_sarray_size(a);
    assert(cap >= sz);
    lean_object * r     = lean_alloc_sarray(esz, sz, cap);
    uint8_t * it     = lean_sarray_cptr(a);
    uint8_t * dest   = lean_sarray_cptr(r);
    memcpy(dest, it, esz*sz);
    lean_dec(a);
    return r;
}

lean_obj_res lean_copy_u32_array(lean_obj_arg a) {
    return lean_copy_sarray_mirror(a, lean_sarray_capacity(a));
}


lean_obj_res lean_sarray_ensure_exclusive_mirror (lean_obj_arg a) {
    if (lean_is_exclusive(a)) {
        return a;
    } else {
        return lean_copy_sarray_mirror(a, lean_sarray_capacity(a));
    }
}

lean_obj_res lean_sarray_deep_copy (lean_obj_arg a) {
    size_t cap = lean_sarray_capacity(a);
    unsigned esz   = lean_sarray_elem_size(a);
    size_t sz      = lean_sarray_size(a);
    assert(cap >= sz);
    lean_object * r     = lean_alloc_sarray(esz, sz, cap);
    uint8_t * it     = lean_sarray_cptr(a);
    uint8_t * dest   = lean_sarray_cptr(r);
    memcpy(dest, it, esz*sz);
    lean_dec(a);
    return r;
}


lean_obj_res lean_sarray_ensure_capacity_mirror (lean_obj_arg a, size_t min_cap, bool exact) {
    size_t cap = lean_sarray_capacity(a);
    if (min_cap <= cap) {
        return a;
    } else {
        return lean_copy_sarray_mirror(a, exact ? min_cap : min_cap * 2);
    }
}

lean_obj_res lean_u32_array_push(lean_obj_arg a, uint32_t d) {
    lean_object * r = lean_sarray_ensure_exclusive_mirror(lean_sarray_ensure_capacity_mirror(a, lean_sarray_size(a) + 1, /* exact */ false));
    size_t sz  = lean_to_sarray(r)->m_size;
    uint32_t * it  = ((uint32_t*) lean_sarray_cptr(r)) + sz;
    *it = d;
    lean_to_sarray(r)->m_size++;
    return r;
}

lean_obj_res lean_u32_array_mk(lean_obj_arg a) {
    size_t sz      = lean_array_size(a);
    lean_obj_res r     = lean_alloc_sarray(sizeof(uint32_t), sz, sz);
    lean_object ** it  = (lean_object **) lean_array_cptr(a);
    lean_object ** end = it + sz;
    uint32_t * dest  = (uint32_t *) lean_sarray_cptr(r);
    for (; it != end; it++, dest++) {
        *dest = lean_unbox_uint32(*it);
    }
    lean_dec(a);
    return r;
}

lean_obj_res lean_u32_array_data(lean_obj_arg a) {
    size_t sz       = lean_sarray_size(a);
    lean_obj_res r      = lean_alloc_array(sz, sz);
    uint32_t * it     = (uint32_t *) lean_sarray_cptr(a);
    uint32_t * end    = it + sz;
    lean_object ** dest = (lean_object **) lean_array_cptr(r);
    for (; it != end; it++, dest++) {
        *dest = lean_box_uint32(*it);
    }
    lean_dec(a);
    return r;
}


lean_obj_res lean_mk_empty_u32_array(b_lean_obj_arg capacity) {
    if (!lean_is_scalar(capacity)) lean_internal_panic_out_of_memory();
    return lean_alloc_sarray(sizeof(uint32_t), 0, lean_unbox(capacity)); // NOLINT
}

lean_obj_res lean_u32_array_size(b_lean_obj_arg a) {
    return lean_box(lean_sarray_size(a));
}

uint32_t * lean_u32_array_cptr(b_lean_obj_arg a) {
    return (uint32_t*)(lean_sarray_cptr(a)); // NOLINT
}



/* Get and set*/


uint32_t lean_u32_array_uget(b_lean_obj_arg a, size_t i) {
    return lean_u32_array_cptr(a)[i];
}

uint32_t lean_u32_array_fget(b_lean_obj_arg a, b_lean_obj_arg i) {
    return lean_u32_array_uget(a, lean_unbox(i));
}

uint32_t lean_u32_array_get(b_lean_obj_arg a, b_lean_obj_arg i) {
    if (lean_is_scalar(i)) {
        size_t idx = lean_unbox(i);
        return idx < lean_sarray_size(a) ? lean_u32_array_uget(a, idx) : 0;
    } else {
        /* The index must be out of bounds. Otherwise we would be out of memory. */
        return 0;
    }
}

lean_obj_res lean_u32_array_uset(lean_obj_arg a, size_t i, uint32_t d) {
    lean_obj_res r;
    if (lean_is_exclusive(a)) r = a;
    else r = lean_copy_u32_array(a);
    uint32_t * it = lean_u32_array_cptr(r) + i;
    *it = d;
    return r;
}

lean_obj_res lean_u32_array_fset(lean_obj_arg a, b_lean_obj_arg i, uint32_t d) {
    return lean_u32_array_uset(a, lean_unbox(i), d);
}

lean_obj_res lean_u32_array_set(lean_obj_arg a, b_lean_obj_arg i, uint32_t d) {
    if (!lean_is_scalar(i)) {
        return a;
    } else {
        size_t idx = lean_unbox(i);
        if (idx >= lean_sarray_size(a)) {
            return a;
        } else {
            return lean_u32_array_uset(a, idx, d);
        }
    }
}


/* Ordered API */


/* Contains */

uint8_t ord_u32_array_contains (b_lean_obj_arg a, uint32_t v) {
    uint32_t * A  = (uint32_t *) lean_sarray_cptr(a);
    uint32_t * end = A + lean_sarray_size(a);
    while (A != end) {
        if (*A < v) {A++;} else {return (*A == v);}        
    }
    return false;
}

uint8_t ord_u32_array_binSearch (b_lean_obj_arg a, uint32_t v) {
    uint32_t * A  = (uint32_t *) lean_sarray_cptr(a);
    size_t start = 0;
    size_t mid;
    size_t end = lean_sarray_size(a);
    while (start < end) {
        mid = (start + end)/2;
        if (mid == start) {return (A[start] == v);} // end = start+1
        else {
            if (A[mid] < v) {start = mid;}
            else {if (A[mid] == v) {return true;}
                  else {end = mid;}}
            }        
    }
    return false;
}

/* Insert */

lean_obj_res ord_u32_array_insert (lean_obj_arg a, uint32_t v) {
    unsigned esz   = lean_sarray_elem_size(a);
    uint32_t * A  = (uint32_t *) lean_sarray_cptr(a);
    uint32_t * abase = A;
    size_t as = lean_sarray_size(a);
    size_t ac = lean_sarray_capacity(a);
    size_t count = 0;
    while (count < as) {
        if (*A < v) {A++; count++;} else {
            if (*A == v) {return a;}
            else { // *A > v
                if (as < ac) {
                    if (lean_is_exclusive(a)) {
                        memmove((A + 1), A, esz*(as - count)); // man pages memcpy requires disjoint memory
                        *A = v;
                        return a;
                    } else {
                        lean_object * r = lean_alloc_sarray(esz, as+1, ac);
                        uint32_t * rbase = (uint32_t*) lean_sarray_cptr(r);
                        memcpy(rbase, abase, esz*count);
                        memcpy((rbase + count + 1), (abase + count), esz*(as - count));
                        rbase = rbase + count;
                        *rbase = v;
                        lean_dec(a);
                        return r;
                    }
                } else {
                    lean_object * r = lean_alloc_sarray(esz, as+1, (2*ac));
                    uint32_t * rbase = (uint32_t*) lean_sarray_cptr(r);
                    memcpy(rbase, abase, esz*count);
                    memcpy((rbase + count + 1), (abase + count), esz*(as - count));
                    rbase = rbase + count;
                    *rbase = v;
                    lean_dec(a);
                    return r;
                }
            }
            }        
    }
    // all entries smaller
    if (as < ac) {
        if (lean_is_exclusive(a)) {
            *A = v;
            return a;
        } else {
            lean_object * r = lean_alloc_sarray(esz, as+1, ac);
            uint32_t * rbase = (uint32_t*) lean_sarray_cptr(r);
            memcpy(rbase, abase, esz*count);
            rbase = rbase + count;
            *rbase = v;
            lean_dec(a);
            return r;
        }
    } else {
        lean_object * r = lean_alloc_sarray(esz, as+1, (2*ac));
        uint32_t * rbase = (uint32_t*) lean_sarray_cptr(r);
        memcpy(rbase, abase, esz*count);
        rbase = rbase + count;
        *rbase = v;
        lean_dec(a);
        return r;
    }
}



lean_obj_res ord_u32_array_binInsert (lean_obj_arg a, uint32_t v) {
    unsigned esz   = lean_sarray_elem_size(a);
    size_t as = lean_sarray_size(a);
    size_t ac = lean_sarray_capacity(a);
    uint32_t * A  = (uint32_t *) lean_sarray_cptr(a);
    size_t start = 0;
    size_t mid;
    size_t end = as;
    while (start < end) {
        mid = (start + end)/2;
        if (mid == start) { // end = start+1
            if (A[start] == v) {
                return a;
            } else {
                if (A[start] < v) {
                    start = start+1;
                    if (as < ac) {
                        if (lean_is_exclusive(a)) {
                            A = A + start;
                            memmove((A + 1), A, esz*(as - start)); // man pages memcpy requires disjoint memory
                            *A = v;
                            return a;
                        } else {
                            lean_object * r = lean_alloc_sarray(esz, as+1, ac);
                            uint32_t * rbase = (uint32_t *) lean_sarray_cptr(r);
                            memcpy(rbase, A, esz*start);
                            memcpy((rbase + start + 1), (A + start), esz*(as - start));
                            rbase = rbase + start;
                            *rbase = v;
                            lean_dec(a);
                            return r;
                        }
                    } else {
                        lean_object * r = lean_alloc_sarray(esz, as+1, (2*ac));
                        uint32_t * rbase = (uint32_t *) lean_sarray_cptr(r);
                        memcpy(rbase, A, esz*start);
                        memcpy((rbase + start + 1), (A + start), esz*(as - start));
                        rbase = rbase + start;
                        *rbase = v;
                        lean_dec(a);
                        return r;
                    }
                } else {
                    // same as above, but no `start = start+1;` since `A[start] > v`
                    if (as < ac) {
                        if (lean_is_exclusive(a)) {
                            A = A + start;
                            memmove((A + 1), A, esz*(as - start)); // man pages memcpy requires disjoint memory
                            *A = v;
                            return a;
                        } else {
                            lean_object * r = lean_alloc_sarray(esz, as+1, ac);
                            uint32_t * rbase = (uint32_t *) lean_sarray_cptr(r);
                            memcpy(rbase, A, esz*start);
                            memcpy((rbase + start + 1), (A + start), esz*(as - start));
                            rbase = rbase + start;
                            *rbase = v;
                            lean_dec(a);
                            return r;
                        }
                    } else {
                        lean_object * r = lean_alloc_sarray(esz, as+1, (2*ac));
                        uint32_t * rbase = (uint32_t *) lean_sarray_cptr(r);
                        memcpy(rbase, A, esz*start);
                        memcpy((rbase + start + 1), (A + start), esz*(as - start));
                        rbase = rbase + start;
                        *rbase = v;
                        lean_dec(a);
                        return r;
                    }
            }
            }
        } else {
            if (A[mid] < v) {start = mid;}
            else {
                if (A[mid] == v) {
                    return a;
                } else {end = mid;}}
            }        
    }
    // start = end
    if (as < ac) {
        if (lean_is_exclusive(a)) {
            *A = v;
            return a;
        } else {
            lean_object * r = lean_alloc_sarray(esz, as+1, ac);
            uint32_t * rbase = (uint32_t *) lean_sarray_cptr(r);
            memcpy(rbase, A, esz*as);
            rbase = rbase + as;
            *rbase = v;
            lean_dec(a);
            return r;
        }
    } else {
        lean_object * r = lean_alloc_sarray(esz, as+1, (2*ac));
        uint32_t * rbase = (uint32_t *) lean_sarray_cptr(r);
        memcpy(rbase, A, esz*as);
        rbase = rbase + as;
        *rbase = v;
        lean_dec(a);
        return r;
    }
}



/* hasCommon */


uint8_t ord_u32_array_hasCommon (b_lean_obj_arg a, b_lean_obj_arg b) {
    uint32_t * A  = (uint32_t *) lean_sarray_cptr(a);
    uint32_t * B  = (uint32_t *) lean_sarray_cptr(b);
    uint32_t * endA = A + lean_sarray_size(a);
    uint32_t * endB = B + lean_sarray_size(b);
    while (A != endA && B != endB) {
        if (*A < *B) {A++;} else {if (*A > *B) {B++;} else {return true;}}        
    }
    return false;
}

/* subsetOf */
uint8_t ord_u32_array_subsetOf (b_lean_obj_arg a, b_lean_obj_arg b) {
    uint32_t * A  = (uint32_t *) lean_sarray_cptr(a);
    uint32_t * B  = (uint32_t *) lean_sarray_cptr(b);
    uint32_t * endA = A + lean_sarray_size(a);
    uint32_t * endB = B + lean_sarray_size(b);
    while (A != endA && B != endB) {
        if (*A < *B) {return false;} else {if (*A > *B) {B++;} else {A++; B++;}}        
    }
    return (A == endA);
}

/* Intersection */

static inline lean_obj_res ord_u32_array_intersect_core (lean_obj_arg mut, lean_obj_arg cons) {
    uint32_t * A  = (uint32_t *) lean_sarray_cptr(mut);
    uint32_t * B  = (uint32_t *) lean_sarray_cptr(cons);
    uint32_t * endA = A + lean_sarray_size(mut);
    uint32_t * endB = B + lean_sarray_size(cons);
    uint32_t * nA  = A;
    size_t count = 0;
    while (A != endA && B != endB) {
        if (*A < *B) {A++;} else {if (*A > *B) {B++;} else {
            *nA = *A;
            nA++; A++; B++; count++;
            }}        
    }
    lean_sarray_set_size(mut, count);
    lean_dec(cons);
    return mut;
}

/* Tries to reuse array, and picks the smaller one if both are exclusive*/
lean_obj_res ord_u32_array_intersect (lean_obj_arg a, lean_obj_arg b) {
    if (lean_is_exclusive(a)) {
        if (lean_is_exclusive(b)) {
            if (lean_sarray_size(a) < lean_sarray_size(b)) {
                ord_u32_array_intersect_core(a,b);
            } else { ord_u32_array_intersect_core(b,a);}
        } else {
            ord_u32_array_intersect_core(a,b);
        }
    } else {
        if (lean_is_exclusive(b)) {
            ord_u32_array_intersect_core(b,a);
        } else {
            size_t sa = lean_sarray_size(a);
            size_t sb = lean_sarray_size(b);
            size_t newSz = ((sa < sb) ? sa : sb);
            lean_object * r = lean_alloc_sarray(lean_sarray_elem_size(a), 0, newSz);
            uint32_t * R  = (uint32_t *) lean_sarray_cptr(r);
            uint32_t * A  = (uint32_t *) lean_sarray_cptr(a);
            uint32_t * B  = (uint32_t *) lean_sarray_cptr(b);
            uint32_t * endA = A + sa;
            uint32_t * endB = B + sb;
            size_t count = 0;
            while (A != endA && B != endB) {
                if (*A < *B) {A++;} else {if (*A > *B) {B++;} else {
                    *R = *A;
                    R++; A++; B++; count++;
                    }}        
            }
            lean_sarray_set_size(r, count);
            lean_dec(a);
            lean_dec(b);
            return r;
        }
    }
}


/* hasDiff */

/* True if a\b is nonempty*/
uint8_t ord_u32_array_hasDiff (b_lean_obj_arg a, b_lean_obj_arg b) {
    uint32_t * A  = (uint32_t *) lean_sarray_cptr(a);
    uint32_t * B  = (uint32_t *) lean_sarray_cptr(b);
    uint32_t * endA = A + lean_sarray_size(a);
    uint32_t * endB = B + lean_sarray_size(b);
    while (A != endA && B != endB) {
        if (*A < *B) {return true;} else {if (*A == *B) {A++;B++;} else {B++;}}        
    }
    return (A != endA);
}

/* Difference */
lean_obj_res ord_u32_array_difference (lean_obj_arg a, b_lean_obj_arg b) {
    if (lean_is_exclusive(a)) {
        uint32_t * A  = (uint32_t *) lean_sarray_cptr(a);
        uint32_t * B  = (uint32_t *) lean_sarray_cptr(b);
        uint32_t * endA = A + lean_sarray_size(a);
        uint32_t * endB = B + lean_sarray_size(b);
        uint32_t * nA  = A;
        size_t count = 0;
        while (A != endA && B != endB) {
            if (*A < *B) {
                *nA = *A;
                nA++; A++; count++;
            } else {if (*A > *B) {B++;} else {
                A++; B++;
                }}        
        }
        while (A != endA) {
            *nA = *A;
            nA++; A++; count++;
        }      
        lean_sarray_set_size(a, count);
        return a;
    } else {
        lean_object * r = lean_alloc_sarray(lean_sarray_elem_size(a), 0, lean_sarray_capacity(a));
        uint32_t * R  = (uint32_t *) lean_sarray_cptr(r);
        uint32_t * A  = (uint32_t *) lean_sarray_cptr(a);
        uint32_t * B  = (uint32_t *) lean_sarray_cptr(b);
        uint32_t * endA = A + lean_sarray_size(a);
        uint32_t * endB = B + lean_sarray_size(b);
        size_t count = 0;
        while (A != endA && B != endB) {
            if (*A < *B) {
                *R = *A;
                R++; A++; count++;
            } else {if (*A > *B) {B++;} else {
                A++; B++;
                }}        
        }
        while (A != endA) {
            *R = *A;
            R++; A++; count++;
        }
        lean_sarray_set_size(r, count);
        lean_dec(a);
        return r;
    }
}



/*Union*/
lean_obj_res ord_u32_array_union (lean_obj_arg a, lean_obj_arg b) {
    size_t newCap = lean_sarray_size(a) + lean_sarray_size(b);
    lean_object * r = lean_alloc_sarray(lean_sarray_elem_size(a), 0, newCap);
    uint32_t * R  = (uint32_t *) lean_sarray_cptr(r);
    uint32_t * A  = (uint32_t *) lean_sarray_cptr(a);
    uint32_t * B  = (uint32_t *) lean_sarray_cptr(b);
    uint32_t * endA = A + lean_sarray_size(a);
    uint32_t * endB = B + lean_sarray_size(b);
    size_t count = 0;
    while (A != endA && B != endB) {
        if (*A < *B) {
                *R = *A;
                R++; A++; count++;
        } else {
            if (*A > *B) {
                    *R = *B;
                    R++; B++; count++;
            } else {
                *R = *A;
                R++; A++; B++; count++;
            }}        
    }
    if (A != endA) {
        while (A != endA) {
            *R = *A;
            R++; A++; count++;
        }
    } else {
        while (B != endB) {
            *R = *B;
            R++; B++; count++;
        }
    }
    lean_sarray_set_size(r, count);
    lean_dec(a);
    lean_dec(b);
    return r;

}

/*Sanitize*/
lean_obj_res ord_u32_array_sanitize (lean_obj_arg a) {
    unsigned esz   = lean_sarray_elem_size(a);
    size_t sz      = lean_sarray_size(a);
    if (sz < lean_sarray_capacity(a)) {
        lean_object * r = lean_alloc_sarray(esz, sz, sz);
        uint32_t * dest = (uint32_t *) lean_sarray_cptr(r);        
        uint32_t * it = (uint32_t *) lean_sarray_cptr(a);
        memcpy(dest, it, esz*sz);
        lean_dec(a);
        return r;
    } else {return a;}
}


/*Shift add*/
lean_obj_res ord_u32_array_shiftAdd (lean_obj_arg a, uint32_t off) {
    if (lean_is_exclusive(a)) {
        uint32_t * A  = (uint32_t *) lean_sarray_cptr(a);
        uint32_t * endA = A + lean_sarray_size(a);
        while ( A != endA) {
            *A += off;
            A++;
        }
        return a;
    } else {
        unsigned esz   = lean_sarray_elem_size(a);
        size_t sz      = lean_sarray_size(a);
        uint32_t * A  = (uint32_t *) lean_sarray_cptr(a);
        uint32_t * endA = A + sz;
        lean_object * r = lean_alloc_sarray(esz, sz, sz);
        uint32_t * R  = (uint32_t *) lean_sarray_cptr(r);
        while (A != endA) {
            *R = *A + off;
            A++; R++;
        }
        lean_dec(a);
        return r;
    }
}

/*Shift sub*/
lean_obj_res ord_u32_array_shiftSub (lean_obj_arg a, uint32_t off) {
    if (lean_is_exclusive(a)) {
        uint32_t * A  = (uint32_t *) lean_sarray_cptr(a);
        uint32_t * endA = A + lean_sarray_size(a);
        while ( A != endA) {
            *A -= off;
            A++;
        }
        return a;
    } else {
        unsigned esz   = lean_sarray_elem_size(a);
        size_t sz      = lean_sarray_size(a);
        uint32_t * A  = (uint32_t *) lean_sarray_cptr(a);
        uint32_t * endA = A + sz;
        lean_object * r = lean_alloc_sarray(esz, sz, sz);
        uint32_t * R  = (uint32_t *) lean_sarray_cptr(r);
        while (A != endA) {
            *R = *A - off;
            A++; R++;
        }
        lean_dec(a);
        return r;
    }
}




size_t u32_array_ptr_get (b_lean_obj_arg a) {return (size_t) lean_sarray_cptr(a); }

uint32_t u32_array_ptr_read (size_t ptr) {
    uint32_t * nptr = ((uint32_t *) ptr);
    return *nptr;
}

size_t u32_array_ptr_set_next (size_t ptr, uint32_t val) {
    uint32_t * nptr = ((uint32_t *) ptr);
    *nptr = val;
    nptr++;
    return (size_t) nptr;
}



/* Array */

lean_obj_res array_squash (lean_obj_arg type, lean_obj_arg a, b_lean_obj_arg from, b_lean_obj_arg num) {
    if (!lean_is_scalar(from) || !lean_is_scalar(num)) {lean_panic("[array_squash] indices not scalar", true);};
    //if (from > to) {lean_panic("[array_squash] index from > to", true);} //could also check that they're in bounds
    lean_object** A = lean_array_cptr(a);
    lean_object* a = lean_ensure_exclusive_array(a);
    {   size_t from = lean_unbox(from);
        size_t num = lean_unbox(num);
        lean_object** dest = A + (from*(sizeof(lean_object*))) ;
        lean_object** src = A + ((from + num)*(sizeof(lean_object*))) ;
        size_t tomove = sizeof(void*)*(lean_array_size(a) - (from + num)); // mimick lean_array_data_byte_size
        memmove(dest,src,tomove);}

}