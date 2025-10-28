int * testnew() {
  int *x;
  x=new int;
  *x=1;
  return x;
}

int * testnewarr() {
  int *x=new int[2];
  x[0]=1;
  x[1]=2;
  return x;
}

void testnewdel() {
  int *x = testnew();
  delete x;
}

void testnewarrdel() {
  int *x = testnewarr();
  delete [] x;
}
