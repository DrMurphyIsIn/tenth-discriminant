/* hcn_classno.c -- COMPUTED class-number data. Exact integer arithmetic only.
   For every fundamental discriminant -d, 3 <= d <= DMAX:
     h_forms(d)     : number of reduced primitive forms (a,b,c), b^2-4ac=-d, |b|<=a<=c, b>=0 if |b|=a or a=c
     h_dirichlet(d) : -(w/(2d)) sum_{n<d} n*(D/n)   (Kronecker symbol; w=6,4,2 for d=3,4,>4)  [if DIRICHLET=1]
     cheapK(d)      : greedy count k of split primes p_1<...<p_k with 4 p_i <= d and 4 p_{k-1} p_k <= d;
                      certificate h >= k+1 without any forms<->ideals bridge.
   Output CSV: d,h_forms,h_dirichlet,cheap_k_plus_1
   Usage: hcn_classno DMAX DIRICHLET(0/1) > out.csv */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static long gcdl(long a, long b){ if(a<0)a=-a; if(b<0)b=-b; while(b){long t=a%b;a=b;b=t;} return a; }

static int kronecker(long D, long n){ /* (D/n), n>=1 */
  int res=1;
  if(n==0) return (D==1||D==-1);
  while(n%2==0){ n/=2; if(D%2==0) return 0; long r=((D%8)+8)%8; if(r==3||r==5) res=-res; }
  long a=((D%n)+n)%n, m=n;
  while(a!=0){
    while(a%2==0){ a/=2; long r=m%8; if(r==3||r==5) res=-res; }
    long t=a; a=m; m=t;
    if(a%4==3 && m%4==3) res=-res;
    a%=m;
  }
  return m==1?res:0;
}

static int is_squarefree(long n){ for(long i=2;i*i<=n;i++) if(n%(i*i)==0) return 0; return 1; }
static int is_fundamental(long d){
  if(d%4==3) return is_squarefree(d);
  if(d%4==0){ long m=d/4; return (m%4==1||m%4==2) && is_squarefree(m); }
  return 0;
}

static long h_forms(long d){
  long cnt=0;
  for(long a=1; 3*a*a<=d; a++){
    for(long b=-a+1; b<=a; b++){
      long num=b*b+d; if(num%(4*a)) continue;
      long c=num/(4*a); if(c<a) continue;
      if(gcdl(gcdl(a,b),c)!=1) continue;
      if(a==c && b<0) continue;
      cnt++;
    }
  }
  return cnt;
}

static long h_dirichlet(long d){
  long s=0; for(long n=1;n<d;n++) s+= n*kronecker(-d,n);
  long w = d==3?6:(d==4?4:2);
  long num=-w*s; if(num%(2*d)) { fprintf(stderr,"DIRICHLET NONINTEGRAL d=%ld\n",d); exit(2);} return num/(2*d);
}

int main(int argc,char**argv){
  long DMAX=atol(argv[1]); int DIR=atoi(argv[2]);
  char*sieve=calloc(DMAX+1,1); for(long i=2;i<=DMAX;i++) sieve[i]=1;
  for(long i=2;i*i<=DMAX;i++) if(sieve[i]) for(long j=i*i;j<=DMAX;j+=i) sieve[j]=0;
  printf("d,h_forms,h_dirichlet,cheap_k_plus_1\n");
  for(long d=3; d<=DMAX; d++){
    if(!is_fundamental(d)) continue;
    long hf=h_forms(d); long hd = DIR? h_dirichlet(d) : -1;
    /* cheap certificate */
    long k=0, last=0;
    for(long p=2; 4*p<=d; p++){ if(!sieve[p]) continue; if(kronecker(-d,p)!=1) continue;
      if(k>0 && 4*p*last>d) break; k++; last=p; }
    printf("%ld,%ld,%ld,%ld\n",d,hf,hd,k+1);
  }
  return 0;
}
