# -*- coding: utf-8 -*-
# Project J-PAKE python implementation
import random
import binascii
import hashlib

class Params():                     # Global params: p,q,g,etc.
    def __init__(self):
        self.pp = 'FD7F53811D75122952DF4A9C2EECE4E7F611B7523CEF4400C31E3F80B6512669455D402251FB593D8D58FABFC5F5BA30F6CB9B556CD7813B801D346FF26660B76B9950A5A49F9FE8047B1022C24FBBA9D7FEB7C61BF83B57E7C6A8A6150F04FB83F6D3C51EC3023554135A169132F675F3AE2B61D72AEFF22203199DD14801C7'
        self.qq = '9760508F15230BCCB292B982A2EB840BF0581CF5'
        self.gg = 'F7E1A085D69B3DDECBBCAB5C36B857B97994AFBBFA3AEA82F9574C0B3D0782675159578EBAD4594FE67107108180B449167123E84C281613B7CF09328CC8A6E13C167A8B547C8D28E0A3AE1E2BB3A675916EA37F0BFA213562F1FB627A01243BCCA4F1BEA8519089A883DFE15AE59F06928B665E807B552564014C3BFECF492A'
        self.p  = int(self.pp,16)
        self.q  = int(self.qq,16)
        self.g  = int(self.gg,16)

def num2str(num, olen):
    if olen is None:
        s = "%x" % num
        if len(s)%2:
            s = "0"+s
        string = binascii.unhexlify(s)
    else:
        fmt_str = "%0" + str(2*olen) + "x"
        string = binascii.unhexlify(fmt_str % num)
        assert len(string) == olen, (len(string), olen)
    return string

def str2num(string):
    return int(binascii.hexlify(string), 16)

class J_PAKE_User():        # A certain party of J-PAKE
    global pa
    def __init__(self, name):
        self.name           =   name
        self.status         =   0       # If there is any error
        self.s              =   0       # Common secret# Alice's x1,x2 or Bob's x3,x4
        # generate x1,x2 with x1 in [0,q) and x2 in [1,q)
        self.x1             =   random.randint(0, pa.q-1)
        self.x2             =   random.randint(1, pa.q-1)
        self.key            =   0       # Caculated key after the algorithm

        # if name=='Alice':
        #   self.x1=int('154C263E99CDDE2F03264DD27F41F514661AB880',16)
        #   self.x2=int('4F36389E1FD58733EBE13287508D7453343C213F',16)
        # else:
        #   self.x1=int('A57A40D6D8DFB8F3715DDE13D62AE6185789D3F',16)
        #   self.x2=int('3461F867D19F423B4EDA4EAE248D587B0C1E57BD',16)

        # for step1
        self.r1             =   0       # Recived g^x3 and zkp of x3
        self.z1             =   [0,0]       
        self.r2             =   0       # Recived g^x4 and zkp of x4
        self.z2             =   [0,0]       
        
        # for step2
        self.A              =   0       # Alice's g^{(x1+x3+x4)*x2*s} or Bob's.....
        self.z3             =   [0,0]   # zkp for x2*s or x4*s
        self.other_key      =   0       # zkp for x2*s or x4*s

        # for multi-party
        self.num            =   0
        self.id             =   0
        self.now            =   0
        self.others         =   [0] * 10
        self.other2         =   0
        self.r1s            =   [0] * 10
        self.z1s            =   [0] * 10
        self.r2s            =   [0] * 10
        self.z2s            =   [0] * 10
        self.z3s            =   [0,0]
        self.k              =   0
        self.l1             =   0
        self.l2             =   0

    def init_with(self, other):         # Alice generate a random common secret with Bob
        self.s  = random.randint(1,pa.q-1)
        other.s = self.s

    def Zhash1(self, g, gr, gx, n):     # A secure one-way hash function from Internet
        def hashbn(bn):
                bns = num2str(bn, None)
                assert len(bns) <= 0xffff
                return num2str(len(bns), 2) + bns
        s = "".join([hashbn(g), hashbn(gr), hashbn(gx),num2str(len(n), 2), n])
        return str2num(hashlib.sha1(s).digest())

    def Zhash2(self, g, gr, gx, n):     # A simple one-way hash function by myself
        re = hashlib.sha1(n)
        re.update(hex(g))
        re.update(hex(gr))
        re.update(hex(gx))
        return str2num(re.digest())

    def Zhash(self, g, gr, gx, n):
        return self.Zhash2(g, gr, gx, n)

    def make_zkp(self, zkp, x, g):              # Create a zkp for x
        r = random.randint(0, pa.q-1)                           # r in [0,q)
        #r = int('13F8CB5FD9071BC1B63AC4405821808905C42D3F',16)

        zkp[0]  =   pow(g, r, pa.p)                             # g^r
        gx      =   pow(g, x, pa.p)                             # g^x       
        h       =   self.Zhash(g, zkp[0], gx, self.name)        # hash
        zkp[1]  =   (r - x*h) % pa.q                            # b = r - x*h

    def check_zkp(self, zkp, x, g, name):
        h       =   self.Zhash(g, zkp[0], x, name)
        t1      =   pow(g, zkp[1], pa.p)
        t2      =   pow(x, h, pa.p)
        t3      =   (t1 * t2) % pa.p
        return t3 == zkp[0]

    def step1(self, other):                 # send g^x1 and g^x2 with zkp
        other.r1            =   pow(pa.g, self.x1, pa.p)
        self.make_zkp(other.z1, self.x1, pa.g)
        other.r2            =   pow(pa.g, self.x2, pa.p)
        self.make_zkp(other.z2, self.x2, pa.g)

    def check1(self, other):
        if self.check_zkp(self.z1, self.r1, pa.g, other.name) and self.check_zkp(self.z2, self.r2, pa.g, other.name):
            print '%s step1 checked ok.' % self.name
        else:
            print 'Failed.'
            self.status=1

    def step2(self, other):
        t1      =   pow(pa.g, self.x1, pa.p)
        t1      =   (t1 * self.r1) % pa.p
        t1      =   (t1 * self.r2) % pa.p
        t2      =   (self.x2 * self.s) % pa.q
        other.A =   pow(t1, t2, pa.p)
        self.make_zkp(other.z3, t2, t1)

    def check2(self, other):
        t1      =   (self.x1 + self.x2) % pa.q
        t2      =   (pow(pa.g, t1, pa.p) * self.r1) % pa.p
        if self.check_zkp(self.z3, self.A, t2, other.name):
            print '%s step2 checked ok.' % self.name
        else:
            print 'Failed.'
            self.status=1

    def compute_key(self):
        t1          =   pow(self.r2, self.x2, pa.p)
        t2          =   pa.q - self.s
        t3          =   pow(t1, t2, pa.p)
        t1          =   (self.A * t3) % pa.p
        self.key    =   pow(t1, self.x2, pa.p)

    def s_hash(self, x):
        return str2num(hashlib.sha1(str(x)).digest())

    def check_key_1(self, other, x):
        other.other_key = x

    def check_key_2(self, other, t):
        x = self.key
        for i in xrange(t):
            x = self.s_hash(x)
        #print x
        #print self.other_key
        self.status += (x == str(self.other_key))

#****************** multi-party add-on **********************
    def step1_multi(self, other):
        nz1 = [0,0]
        nz2 = [0,0]

        other.r1s[self.id]=pow(pa.g, self.x1, pa.p)
        self.make_zkp(nz1, self.x1, pa.g)
        other.r2s[self.id]=pow(pa.g, self.x2, pa.p)
        self.make_zkp(nz2, self.x2, pa.g)

        other.z1s[self.id]=nz1
        other.z2s[self.id]=nz2
        other.others[self.id]=self.name


    def check1_multi(self):
        for i in xrange(self.num):
            if i!=self.id:
                if self.check_zkp(self.z1s[i], self.r1s[i], pa.g, self.others[i]) and self.check_zkp(self.z2s[i], self.r2s[i], pa.g, self.others[i]):
                    print '%s - %s step1 checked ok.' % (self.name,self.others[i])
                else:
                    self.status=1
                    print 'error!'

    def step2_multi(self, other):
        t1      =   pow(pa.g, self.x1, pa.p)
        for i in xrange(self.num):
            if i!=self.id:
                t1  =   (t1 * self.r1s[i]) % pa.p
        for i in xrange(self.num):
            if i!=self.id:
                t1  =   (t1 * self.r2s[i]) % pa.p
        t2      =   (self.x2 * self.s) % pa.q
        other.A =   pow(t1, t2, pa.p)
        other.other2 = self.x2
        self.make_zkp(other.z3s, t2, t1)

    def check2_multi(self, other):
        t1      =   (self.x1 + self.x2) % pa.q
        t2      =   pow(pa.g, t1, pa.p)
        for i in xrange(self.num):
            if i!=other.id and i!=self.id:
                t2  =   (t2 * self.r2s[i]) % pa.p
        for i in xrange(self.num):
            if i!=self.id:
                t2  =   (t2 * self.r1s[i]) % pa.p        
        if self.check_zkp(self.z3s, self.A, t2, other.name):
            print '%s - %s step2 checked ok.' % (self.name, other.name)
        else:
            print 'Failed.'
            self.status=1

    def compute_key1_multi(self):
        t1          =   pow(self.l1, self.x2, pa.p)
        t2          =   pa.q - self.s
        t3          =   pow(t1, t2, pa.p)
        t1          =   (self.A * t3) % pa.p
        # self.k = t3
        self.k      =   pow(t1, self.x2, pa.p)


#********************************* class over ********************************************

def loop_send(users, re, f, e, n):
    if f==e:
        return re
    return loop_send(users, pow(re, users[f].x2, pa.p), (f+1)%n, e, n)

# def loop_send2(users, re, f, e, n):
#     if f==e:
#         return re
#     return loop_send2(users, pow(re, users[f].x2, pa.p), (f+1)%n, e, n)

def multi_jpake(users):
    n = len(users)

    for i in xrange(n):
        users[i].id = i
        users[i].num = n

    users[0].init_with(users[1])
    for i in users[2:]:
        i.s = users[0].s

    # first round
    for i in users:
        for j in xrange(n):
            if i.id != j:
                i.step1_multi(users[j])

    for i in users:
        print i.name,i.id
    print ''

    for i in users:
        i.check1_multi()

    print ''

    # second round
    for i in xrange(n):
        users[i].step2_multi(users[(i+1)%n])

    for i in xrange(n):
        users[i].check2_multi(users[(i+n-1)%n])

    # print users[1].A
    # for j in xrange(3):
    #     now = 0
    #     for i in users:
    #         now += i.x1+i.x2
    #     now = (now - users[(j+2)%3].x2) % pa.q
    #     t1 = pow(pa.g, now, pa.p)
    #     t1 = pow(t1, users[(j+2)%3].x2, pa.p)
    #     t1 = pow(t1, users[0].s, pa.p)
    #     A=t1
    #     now = pow(pow(pa.g, users[0].x2, pa.p), users[1].x2, pa.p)
    #     t1 = pow(now, users[2].x2, pa.p)
    #     t1 = pow(t1, (pa.q-users[0].s)%pa.q, pa.p)
    #     A=(A*t1)%pa.p
    #     A=pow(A,users[j].x2,pa.p)
    #     A=pow(A,users[(j+1)%3].x2,pa.p)
    #     print A

    # third round
    for i in xrange(n):
        users[i].l1 = loop_send(users, pow(pa.g, users[(i+1)%n].x2, pa.p), (i+2)%n, i, n)

    for i in users:
        i.compute_key1_multi()

    # print users[1].l1
    # now = pow(pow(pa.g, users[2].x2, pa.p), users[0].x2, pa.p)
    # t1 = pow(now, users[1].x2, pa.p)
    # t1 = pow(t1, pa.q-users[0].s, pa.p)
    # print t1
    # for i in users:
    #     print pow(pow(i.l1, i.x2, pa.p), pa.q - i.s, pa.p)
    #     print i.k
    # for i in xrange(n):
    #     print pow(users[i].k, users[(i+1)%n].x2, pa.p)
    # now = (users[0].x1 + users[1].x1 + users[2].x1) % pa.q
    # t1 = pow(pa.g, now, pa.p)
    # t1 = pow(t1, users[0].x2, pa.p)
    # t1 = pow(t1, users[2].x2, pa.p)
    # t1 = pow(t1, users[2].s, pa.p)
    # print t1
    # print users[0].k

    # fourth round
    for i in xrange(n):
        users[i].key = loop_send(users, users[i].k, (i+1)%n, (i+n-1)%n, n)

    print ""

    for i in users:
        if i.key!=users[0].key:
            print 'no'
        # print i.key

#********************************************************************************
def do_jpake(Alice, Bob):
    Alice.init_with(Bob)

    print 'Their common s is ',hex(Alice.s)

    # step 1
    Alice.step1(Bob)
    Bob.step1(Alice)
    Alice.check1(Bob)
    Bob.check1(Alice)

    if (Alice.status + Bob.status):
        print 'any thing wrong!'
        exit(0)

    # step 2
    Alice.step2(Bob)
    Bob.step2(Alice)
    Alice.check2(Bob)
    Bob.check2(Alice)

    if (Alice.status + Bob.status):
        print 'any thing wrong!'
        exit(0)

    # All done, compute and check the key
    Alice.compute_key()
    Bob.compute_key()

    Alice.check_key_1(Bob, Alice.s_hash(Alice.s_hash(Alice.key)))
    Bob.check_key_1(Alice, Bob.s_hash(Bob.key))

    Alice.check_key_2(Bob, 1)
    Bob.check_key_2(Alice, 2)

    if Alice.status + Bob.status:
        print 'any thing wrong!'
        exit(0)

    print 'Key checked ok!'

    print 'J-PAKE successfully done, the common key is computed as \n',hex(Alice.key)


#********************************************************************************
#********************************************************************************
#********************************** main *****************************************
#********************************************************************************
#********************************************************************************
pa      =       Params()
if __name__ == '__main__':
    testing_multi = 0
#*************************** multi-test ************************************
    if testing_multi:
        Alice   =       J_PAKE_User('Alice')
        Bob     =       J_PAKE_User('Bob')
        Carlos  =       J_PAKE_User('Carlos')
        
        users   =       [Alice, Bob, Carlos]

        multi_jpake(users)


    else:
#*************************** normal ***********************************
        Alice   =       J_PAKE_User('Alice')
        Bob     =       J_PAKE_User('Bob')
        do_jpake(Alice, Bob)