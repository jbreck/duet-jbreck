int __cost;

void loop (int n) {
    int i,j;
    for (i=0; i<n; i++){
        for(j=0;j<n; j++){
            __cost++;
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
