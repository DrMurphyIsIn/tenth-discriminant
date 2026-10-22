/* Independent class numbers h(-d) by counting reduced primitive forms (a,b,c), b^2-4ac=-d,
   |b|<=a<=c, b>=0 if |b|==a or a==c.  Written from the definition, separately from hcn_classno.c.
   Output: d,h for every fundamental -d, 3 <= d <= DMAX (classno_340000_independent.csv is its output for 340000).
   Usage: independent_classno DMAX > out.csv */
#include <stdio.h>
#include <stdlib.h>
static long g(long a,long b){ if(a<0)a=-a; if(b<0)b=-b; while(b){long t=a%b;a=b;b=t;} return a; }
static int sqfree(long n){ for(long p=2;p*p<=n;p++){ if(n%(p*p)==0) return 0; } return 1; }
static int fundamental(long d){ /* -d fundamental */
  if(d%4==3) return sqfree(d);
  if(d%4==0){ long m=d/4; return (m%4==1||m%4==2) && sqfree(m); }
  return 0; }
int main(int argc,char**argv){
  long D=atol(argv[1]);
  int *h=calloc(D+1,sizeof(int));
  for(long a=1; 3*a*a<=D; a++)
    for(long b=-a+1; b<=a; b++){
      for(long c=a; ; c++){
        long d=4*a*c-b*b; if(d>D) break;
        if(d<=0) continue;
        if((b<0) && (c==a)) continue;
        if(g(g(a,b),c)!=1) continue;
        h[d]++;
      }
    }
  for(long d=3; d<=D; d++) if(fundamental(d)) printf("%ld,%d\n", d, h[d]);
  return 0; }
