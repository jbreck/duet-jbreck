int __cost;

void loop (int n) {
    int i,j,k,l,m;
    for (i=0; i<n; i++){
        for(j=0;j<n; j++){
            for(k=0;k<n;k++) {
                for(l=0;l<n;l++){
                    for(m=0;m<n;m++){
                        __cost++;
                    }
                }
            }
        }
    }
}

void recursive(int n) {
    loop(n);
    if (n <= 1) {return;}
    recursive(n/2);
}
void main(int n) {
    recursive(n);
}
