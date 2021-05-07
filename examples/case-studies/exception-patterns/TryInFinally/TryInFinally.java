//:: cases TryInFinally
//:: tools silicon
//:: verdict Pass


import java.io.IOException;

class TryInFinally {
    int x;

    boolean randomBoolean();
    
    //@ context_everywhere Perm(x, write);
    //@ signals (ArithmeticException e) x == 31 || x == 32;
    //@ signals (ArrayStoreException e) x == 111 || x == 112;
    //@ ensures x == 32;
    int  m() {
        x = 0;

        boolean throwB1 = randomBoolean();
        boolean throwB2 = randomBoolean();

        try {
            if (throwB1) {
                x += 1;
                throw new ArithmeticException();
            }

            x += 2;
        } finally {
            try {
                x += 10;

                if (throwB2) {
                    throw new Exception();
                }
                
                x += 20;
            } catch (Exception e) {
                x += 100;
                throw new ArrayStoreException();
            }
        }
    }
}









