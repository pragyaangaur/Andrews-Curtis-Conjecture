import sys, itertools
sys.path.insert(0, '.')
sys.path.insert(0, '../../../../survey')
import nielsen_census as nc
a = tuple([1,2,3,4,0]); b = tuple([1,2,0,3,4])
t = nc.table_of_permutations("A5", 5, [a,b])
st = nc.Structure(t); st.precompute()
for (conj, inv, name) in ((False, False, 'prg'), (False, True, 'prg_inv'),
                          (True, False, 'niels_census_noconj'), (True, True, 'ac')):
    comp, sizes, verts = nc.graph_components(st, 2, with_conjugation=conj,
                                             with_inversion=inv, mode="generate")
    print(name, len(sizes), sorted(sizes, reverse=True))
