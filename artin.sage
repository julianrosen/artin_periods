load("../recurrence/recurrence.sage")

def compositum(K,L):
    # If K and L are number fields, compositum(K,L) is a triple
    # (J,f,g), where J is a number field and f:K-->J, g:L-->J
    y,z = K.gens()[0],L.gens()[0]
    f = z.minpoly()
    R.<t> = PolynomialRing(K)
    J.<x> = f(t).splitting_field()
    f,g = list(Hom(K,J))[0],list(Hom(L,J))[0]
    assert f.domain() is K
    assert g.domain() is L
    assert f.codomain() is J
    assert g.codomain() is J
    return (J,f,g)

def restrict(h,f):
    # f: K --> L, h in Gal(L/Q), restrict(h,f) in Gal(K/Q)
    # is the restriction of h along f.
    K,L = f.domain(),f.codomain()
    if not K.is_galois() or not L.is_galois():
        raise ValueError("The domain and codomain of f must be Galois over Q")
    x = K.gens()[0]
    G,H = K.galois_group(),L.galois_group()
    for g in G:
        if h(f(x)) == f(g(x)):
            return g
    # This should not happen
    raise Exception("Could not restrict")

Number = (Integer,Rational)

class ArtPer(Ring):
    # Element = ArtPerElement
    def __init__(self):
        Ring.__init__(self,base=QQ)
        self._populate_coercion_lists_()
        
    def _repr_(self):
        return "The ring of de Rham motivic periods of Artin type over Q"
    
    def _element_constructor_(self,s):
        return ArtPerElement(self,s)
    
    def _coerce_map_from_(self,S):
        if QQ.coerce_map_from(S):
            return True
        elif isinstance(S,ArtPer):
            return True
        elif isinstance(S,Recurrence) and QQ.coerce_map_from(S.base()):
            return True
        print "Coercion failed: ",S,parent(S)
        return False
    

class ArtPerElement(RingElement):
    """Objects of this class are de Rham motivic periods of
    the category of Artin motives over Q"""
    def __init__(self,parent,s):
        RingElement.__init__(self,parent)
        if isinstance(s,Number):
            try:
                self.field = PolynomialRing(QQ,'x').one().splitting_field('x')
            except:
                print "Field failed"
            self.gen = self.field.gens()[0]
            self.D = {self.group().an_element():QQ(s)}
            self.desc = str(s)
        elif isinstance(s,ArtPerElement):
            self.field = s.field
            self.gen = s.gen
            self.D = dict(s.D)
            self.desc = str(s.desc)
            self.clean()
        elif isinstance(s,dict):
            self.field = s.keys()[0].as_hom().domain()
            self.gen = self.field.gens()[0]
            self.D = dict(s)
            self.desc = str(s)
            self.clean()
        elif isinstance(s,RecurrenceElement) and (s.base() is QQ or s.base() is ZZ):
            self.field = s.splitting_field()
            L = s.L_L()
            self.D = {g: sum(s[0]*g(s[1]) for s in L) for g in self.field.galois_group()}
            self.gen = self.field.gens()[0]
            self.desc = "The de Rham motivic period associated with a recurrent sequence"
            self.clean()
        else:
            # Assume s is a matrix
            try:
                M = s
                m,n = M.dimensions()
                assert m == n
                f = M.characteristic_polynomial()
                R.<x> = PolynomialRing(QQ)
                L.<x> = f(x).splitting_field()
                D,A = M.jordan_form(L,transformation=True)
                assert A*D*A.inverse() == M
                Mp = [[0 for i in range(n)] for j in range(n)]
                for i in range(n):
                    for j in range(n):
                        T = ArtPerElement(parent,0)
                        T.field = L
                        T.D = {}
                        for g in T.group():
                            T.D[g] = sum(A[(i,k)]*g(D[(k,k)])*A.inverse()[(k,j)] for k in range(n))
                        T.clean()
                        Mp[i][j] = T
                return Mp
            except:
                raise ValueError('Cannot construct de Rham period from type '+str(type(s)))
    
    def group(self):
        return self.field.galois_group()
    
    def _repr_(self):
        return 'A de Rham motivic period of Artin type'
    
    def clean(self):
        S = self.field.subfields()
        S = [(s[0],s[1]) for s in S]
        S.sort(key=lambda s:s[0].degree())
        for L,f in S:
            for g in self.D:
                try:
                    L(self.D[g])
                except:
                    break
            else:
                D = {}
                for g in self.D:
                    rho = restrict(g,f)
                    r = L(self.D[g])
                    if rho in D and D[rho] != r:
                        break
                    else:
                        D[rho] = r
                else:
                    self.D = D
                    self.field = L
                    return self
        return self
       
    
    def extend_field(self,f):
        K,L = f.domain(),f.codomain()
        assert self.field is K
        assert L.is_galois()
        D = {}
        for h in L.galois_group():
            rho = restrict(h,f)
            assert rho in K.galois_group()
            if rho not in self.D:
                print self.field
                print rho
                print self.D
                raise Exception("Error")
            D[h] = f(self.D[restrict(h,f)])
        T = ArtPerElement(parent(self),0)
        T.D = D
        T.field = L
        return T
    
    def _add_(self, s):
        T = s
        #T = ArtPerElement(s)
        J,f,g = compositum(self.field,T.field)
        selfE,TE = self.extend_field(f),T.extend_field(g)
        assert selfE.field is J and TE.field is J
        for x in TE.D:
            TE.D[x] += selfE.D[x]
        return TE
    
    def __eq__(self,other):
        if isinstance(other,ArtPerElement):
            s = other
        elif parent(self).coerce_map_from(parent(other)):
            s = parent(self)(other)
        else:
            raise ValueError("Connot compare elements")
        J,f,g = compositum(self.field,s.field)
        D1,D2 = self.extend_field(f).D,s.extend_field(g).D
        for x in D1:
            assert x in D2
            assert parent(D1[x]) is parent(D2[x])
            if D1[x] != D2[x]:
                return (D1,D2)
                return False
        return True
    
    def _mul_(self, s):
        T = s
        #T = ArtPer(s)
        J,f,g = compositum(self.field,T.field)
        selfE,TE = self.extend_field(f),T.extend_field(g)
        assert selfE.field is J and TE.field is J
        for x in TE.D:
            TE.D[x] *= selfE.D[x]
        return TE
    
    def _sub_(self,s):
        return self + (-1)*s
    def _pow_(self,n):
        if n == 0:
            return ArtPerElement(1)
        elif n > 0:
            return self*self**(n-1)
        elif n < 0:
            return (self^(-n)).inv()
    
    def disp(self):
        print "Function on the Galois group of ",self.field
        for g in self.D:
            print g," maps to ",self.D[g]
        return None
    

    
    def inv(self):
        if not self.is_inv():
            raise ValueError("Element is not invertible")
        T = ArtPerElement(self.parent(),self)
        for x in T.D:
            T.D[x] = T.D[x]^(-1)
        return T
    
    def is_inv(self):
        for x in self.D:
            if self.D[x] == 0:
                return False
        return True
    
    def _div_(self, s):
        if isinstance(s,Number):
            return self*(Rat(1)/s)
        else:
            return self * s.inv()
        
    def minimal_polynomial(self):
        L = [self.D[x].minpoly() for x in self.D]
        return lcm(L)
    

def M_to_p(M):
    """Returns matrix with entries in ArtPer
    image under per_A is M^p mod p"""
    m,n = M.dimensions()
    assert m == n
    var('x')
    f = M.characteristic_polynomial()
    R.<x> = PolynomialRing(QQ)
    L.<x> = f(x).splitting_field()
    D,A = M.jordan_form(L,transformation=True)
    assert A*D*A.inverse() == M
    Mp = [[0 for i in range(n)] for j in range(n)]
    for i in range(n):
        for j in range(n):
            T = ArtPerElement(0)
            T.field = L
            T.D = {}
            for g in T.group():
                T.D[g] = sum(A[(i,k)]*g(D[(k,k)])*A.inverse()[(k,j)] for k in range(n))
            T.clean()
            Mp[i][j] = T
    return Mp