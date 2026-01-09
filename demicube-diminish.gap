DnDiminish := function(n)
    local gens, G, verts, adjacent, illegalcs, seen, Hc, H, vos, keepi, checki, good, v, adjs, canon, sym;
    gens := Concatenation([(1,n+2)(2,n+1)], List([1..n-1], i -> (i,i+1)(i+n,i+n+1)));
    G := Group(gens);
    verts := Orbit(G, [1..n], OnSets);
    adjacent := {v1, v2} -> Length(Intersection(v1, v2)) = n-2;
    # illegalcs := Orbit(G, Set(List([1..n],x->Concatenation([1..n-1],[n*2]))+IdentityMat(n-1)*n, Set), OnSetsSets);
    # one vertex is assumed to be present
    illegalcs := Orbit(G, Set(List([1..2],x->Concatenation([1..n-1],[n*2]))+IdentityMat(2)*n, Set), OnSetsSets);
    seen := [];
    for Hc in ConjugacyClassesSubgroups(G) do
        H := Representative(Hc);
        vos := OrbitsDomain(H, verts, OnSets);
        # for one representative vertex in each orbit, check whether not diminishing one other orbit gives an illegal configuration
        for keepi in [1..Length(vos)] do
            if Length(vos[keepi]) = Length(verts) then break; fi;
            good := true;
            for checki in [1..Length(vos)] do
                if checki = keepi then continue; fi;
                v := vos[checki][1];
                adjs := Difference(Filtered(verts, w -> adjacent(v, w)), vos[keepi]);
                if ForAny(illegalcs, c -> IsSubset(adjs, c)) then
                    good := false;
                    break;
                fi;
            od;
            if not good then continue; fi;
            canon := Minimum(Orbit(G, Set(vos[keepi]), OnSetsSets));
            if not (canon in seen) then
                AddSet(seen, canon);
                sym := Stabilizer(G, Set(vos[keepi]), OnSetsSets);
                Print(Length(vos[keepi]), " vertices (order ", Size(sym), "): ", vos[keepi][1], " with ", GeneratorsOfGroup(H), "\n");
            fi;
        od;
    od;
    # return G;
end;

ToCoords := function(n, vert, gens)
    local toVec;
    toVec := function(i)
        if i <= n then
            return IdentityMat(n)[i];
        else
            return -IdentityMat(n)[i-n];
        fi;
    end;
    return List(Orbit(Group(gens), vert, OnSets), v -> Sum(v, toVec));
end;


# DnDiminish := function(n)
#     local gens, G, verts, hom, Gv, adjacent, illegalcs, seen, Hc, H, vos, keepi, checki, good, v, adjs, canon, sym;
#     gens := Concatenation([(1,n+2)(2,n+1)], List([1..n-1], i -> (i,i+1)(i+n,i+n+1)));
#     G := Group(gens);
#     verts := Orbit(G, [1..n], OnSets);
#     hom := ActionHomomorphism(G, verts, OnSets);
#     Gv := Image(hom);
#     adjacent := {v1, v2} -> Length(Intersection(verts[v1], verts[v2])) = n-2;
#     # illegalcs := Orbit(G, Set(List([1..n],x->Concatenation([1..n-1],[n*2]))+IdentityMat(n-1)*n, Set), OnSetsSets);
#     # one vertex is assumed to be present
#     illegalcs := Orbit(G, Set(
#         List([1..2],x->Concatenation([1..n-1],[n*2]))+IdentityMat(2)*n, 
#         v -> Position(verts, Set(v))
#     ), OnSets);
#     seen := [];
#     for Hc in ConjugacyClassesSubgroups(Gv) do
#         H := Representative(Hc);
#         vos := Orbits(H);
#         # for one representative vertex in each orbit, check whether not diminishing one other orbit gives an illegal configuration
#         for keepi in [1..Length(vos)] do
#             if Length(vos[keepi]) = NrMovedPoints(Gv) then break; fi;
#             good := true;
#             for checki in [1..Length(vos)] do
#                 if checki = keepi then continue; fi;
#                 v := vos[checki][1];
#                 adjs := Difference(Filtered([1..NrMovedPoints(Gv)], w -> adjacent(v, w)), vos[keepi]);
#                 if ForAny(illegalcs, c -> IsSubset(adjs, c)) then
#                     good := false;
#                     break;
#                 fi;
#             od;
#             if not good then continue; fi;
#             canon := Minimum(Orbit(Gv, Set(vos[keepi]), OnSets));
#             if not (canon in seen) then
#                 AddSet(seen, canon);
#                 sym := Stabilizer(Gv, Set(vos[keepi]), OnSets);
#                 Print(Length(vos[keepi]), " vertices (order ", Size(sym), "): ", verts[vos[keepi][1]], " with ", GeneratorsOfGroup(PreImage(hom, H)), "\n");
#             fi;
#         od;
#     od;
#     # return G;
# end;
