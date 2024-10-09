#include<stdio.h>
#include <stdint.h>
void helloWorld() {
    printf("Hello, World!\n");
}


void firstCall(uint32_t num1, uint32_t num2) {

  if (num1 > 50 && num1 <100){
        int x = num1 * 10;
        if (x < num2 && num2 <2000){
            helloWorld();
        }
    }

}
