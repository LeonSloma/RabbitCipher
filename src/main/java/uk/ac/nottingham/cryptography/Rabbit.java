package uk.ac.nottingham.cryptography;

public class Rabbit implements RabbitCipher {

    long WORDSIZE = 0xFFFFFFFFl;

    // state variables
    int[] x;

    // counter
    int[] c;
    // carry bit
    byte b;

    int[] x_master;
    int[] c_master;
    byte b_master;

    // constants
    int[] a = new int[] {
            0x4D34D34D, //A0
            0xD34D34D3, //A1
            0x34D34D34, //A2
            0x4D34D34D, //A3
            0xD34D34D3, //A4
            0x34D34D34, //A5
            0x4D34D34D, //A6
            0xD34D34D3  //A7
    };

    @Override
    public void initialiseCipher(byte[] key) {
        int index;

        x = new int[8];
        c = new int[8];
        b = 0;

        for (int j=0; j<8; j++) {
            // if j is even
            if(j%2 == 0) {

                // Xj = K(j+1 mod 8) || Kj
                x[j] = toBytePairInt(key[j*2+1], key[j*2]) & 0xFFFF;
                index = 2 * ((j+1) % 8);
                x[j] |= toBytePairInt(key[index+1], key[index]) << 16;

                // Cj = K(j+4 mod 8) || K(j+5 mod 8)
                index = 2 * ((j+5) % 8);
                c[j] = toBytePairInt(key[index+1], key[index]) & 0xFFFF;
                index = 2 * ((j+4) % 8);
                c[j] |= toBytePairInt(key[index+1], key[index]) << 16;
            } else {

                // Xj = K(j+5 mod 8) || K(j+4 mod 8)
                index = 2 * ((j + 4) % 8);
                x[j] = toBytePairInt(key[index+1], key[index]) & 0xFFFF;
                index = 2 * ((j + 5) % 8);
                x[j] |= toBytePairInt(key[index+1], key[index]) << 16;

                // Cj = Kj || K(j+1 mod 8)
                index = 2 * ((j + 1) % 8);
                c[j] = toBytePairInt(key[index+1], key[index]) & 0xFFFF;
                c[j] |= toBytePairInt(key[j*2+1], key[j*2]) << 16;
            }
        }

        // system iterated 4 times
        for (int i=0; i<4; i++) {
            counterUpdate();
            nextState();
        }

        // counter reinitialised
        for (int j=0; j<8; j++) {
            // Cj = Cj ^ X(j+4 mod 8)
            c[j] = c[j] ^ x[(j+4) % 8];
        }

        // set master state values
        x_master = x.clone();
        c_master = c.clone();
        b_master = b;
    }

    @Override
    public void initialiseIV(byte[] iv) {
        if (iv == null) return;

        // set state to master state
        x = x_master.clone();
        c = c_master.clone();
        b = b_master;

        c[0] = c[0] ^ ((iv[0] & 0xFF) | (iv[1] & 0xFF) << 8 | (iv[2] & 0xFF) << 16 | (iv[3] & 0xFF) << 24); //C0 = C0 ^ IV[31..0]
        c[1] = c[1] ^ ((iv[2] & 0xFF) | (iv[3] & 0xFF) << 8 | (iv[6] & 0xFF) << 16 | (iv[7] & 0xFF) << 24); //C1 = C1 ^ (IV[63..48] || IV[31..16])
        c[2] = c[2] ^ ((iv[4] & 0xFF) | (iv[5] & 0xFF) << 8 | (iv[6] & 0xFF) << 16 | (iv[7] & 0xFF) << 24); //C2 = C2 ^ IV[63..32]
        c[3] = c[3] ^ ((iv[0] & 0xFF) | (iv[1] & 0xFF) << 8 | (iv[4] & 0xFF) << 16 | (iv[5] & 0xFF) << 24); //C3 = C3 ^ (IV[47..32] || IV[15..0])
        c[4] = c[4] ^ ((iv[0] & 0xFF) | (iv[1] & 0xFF) << 8 | (iv[2] & 0xFF) << 16 | (iv[3] & 0xFF) << 24); //C4 = C4 ^ IV[31..0]
        c[5] = c[5] ^ ((iv[2] & 0xFF) | (iv[3] & 0xFF) << 8 | (iv[6] & 0xFF) << 16 | (iv[7] & 0xFF) << 24); //C5 = C5 ^ (IV[63..48] || IV[31..16])
        c[6] = c[6] ^ ((iv[4] & 0xFF) | (iv[5] & 0xFF) << 8 | (iv[6] & 0xFF) << 16 | (iv[7] & 0xFF) << 24); //C6 = C6 ^ IV[63..32]
        c[7] = c[7] ^ ((iv[0] & 0xFF) | (iv[1] & 0xFF) << 8 | (iv[4] & 0xFF) << 16 | (iv[5] & 0xFF) << 24); //C7 = C7 ^ (IV[47..32] || IV[15..0])

        // system iterated 4 times
        for (int i=0; i<4; i++) {
            counterUpdate();
            nextState();
        }
    }

    @Override
    public final void counterUpdate() {
        long temp = 0;

        for (int j=0; j<8; j++) {
//            temp = Cj + Aj + b
//            b    = temp div WORDSIZE
//            Cj   = temp mod WORDSIZE
            temp = (c[j] & WORDSIZE) + (a[j] & WORDSIZE) + b;
            b = (byte) (temp >>> 32);
            c[j] = (int) (temp & WORDSIZE);
        }

    }

    @Override
    public final void nextState() {
        int[] g = new int[8];


        for (int j=0; j<8; j++) {
            // Gj = g(Xj,Cj)
            g[j] = gFunc(x[j], c[j]);
        }

        x[0] = (int) ((g[0] + rotatel(g[7], 16) + rotatel(g[6],16))& WORDSIZE); //X0 = G0 + (G7 <<< 16) + (G6 <<< 16) mod WORDSIZE
        x[1] = (int) ((g[1] + rotatel(g[0], 8)  +         g[7])       & WORDSIZE); //X1 = G1 + (G0 <<<  8) +  G7         mod WORDSIZE
        x[2] = (int) ((g[2] + rotatel(g[1], 16) + rotatel(g[0],16))& WORDSIZE); //X2 = G2 + (G1 <<< 16) + (G0 <<< 16) mod WORDSIZE
        x[3] = (int) ((g[3] + rotatel(g[2], 8)  +         g[1])       & WORDSIZE); //X3 = G3 + (G2 <<<  8) +  G1         mod WORDSIZE
        x[4] = (int) ((g[4] + rotatel(g[3], 16) + rotatel(g[2],16))& WORDSIZE); //X4 = G4 + (G3 <<< 16) + (G2 <<< 16) mod WORDSIZE
        x[5] = (int) ((g[5] + rotatel(g[4], 8)  +         g[3])       & WORDSIZE); //X5 = G5 + (G4 <<<  8) +  G3         mod WORDSIZE
        x[6] = (int) ((g[6] + rotatel(g[5], 16) + rotatel(g[4],16))& WORDSIZE); //X6 = G6 + (G5 <<< 16) + (G4 <<< 16) mod WORDSIZE
        x[7] = (int) ((g[7] + rotatel(g[6], 8)  +         g[5])       & WORDSIZE); //X7 = G7 + (G6 <<<  8) +  G5         mod WORDSIZE
    }

    // g(u,v) = LSW(square(u+v)) ^ MSW(square(u+v))
    private int gFunc(int u, int v) {
        long squ = square(u,v);
        int lsw = (int)squ;
        int msw = (int)(squ >>> 32);

        return lsw ^ msw;
    }

    // square(u+v) = ((u+v mod WORDSIZE) * (u+v mod WORDSIZE))
    private long square( int u, int v ) {
        long mod = (u+v) & WORDSIZE;
        return mod * mod;
    }

    @Override
    public void encrypt(byte[] block) {
        encryptDecrypt(block);
    }

    @Override
    public void decrypt(byte[] block) {
        encryptDecrypt(block);
    }

    protected void encryptDecrypt(byte[] block) {

        short[] s = null;

        for (int j=0; j<block.length; j++) {

            // round = 16 loop iterations (16 bytes)
            if (j%16 == 0) {
                // iterate system, then generate s block
                counterUpdate();
                nextState();
                s = generateBlock();
            }

            // perform xor encryption / decryption
            if (j % 2 == 0)
                block[j] = (byte) (block[j] ^ (s[(j/2) % 8] & 0xFF));
            else
                block[j] = (byte) (block[j] ^ (s[(j/2) % 8] >>> 8));
        }
    }

    private short[] generateBlock() {
        short[] s = new short[8];

        s[0] = (short) ((x[0] & 0xFFFF) ^ (x[5] >>> 16));   //S[15..0]    = X0[15..0]  ^ X5[31..16]
        s[1] = (short) ((x[0] >>> 16)   ^ (x[3] & 0xFFFF)); //S[31..16]   = X0[31..16] ^ X3[15..0]
        s[2] = (short) ((x[2] & 0xFFFF) ^ (x[7] >>> 16));   //S[47..32]   = X2[15..0]  ^ X7[31..16]
        s[3] = (short) ((x[2] >>> 16)   ^ (x[5] & 0xFFFF)); //S[63..48]   = X2[31..16] ^ X5[15..0]
        s[4] = (short) ((x[4] & 0xFFFF) ^ (x[1] >>> 16));   //S[79..64]   = X4[15..0]  ^ X1[31..16]
        s[5] = (short) ((x[4] >>> 16)   ^ (x[7] & 0xFFFF)); //S[95..80]   = X4[31..16] ^ X7[15..0]
        s[6] = (short) ((x[6] & 0xFFFF) ^ (x[3] >>> 16));   //S[111..96]  = X6[15..0]  ^ X3[31..16]
        s[7] = (short) ((x[6] >>> 16)   ^ (x[1] & 0xFFFF)); //S[127..112] = X6[31..16] ^ X1[15..0]

        return s;
    }

    @Override
    public void encryptMessage(byte[] iv, byte[] message) {
        initialiseIV(iv);
        encrypt( message );
    }


    @Override
    public void decryptMessage(byte[] iv, byte[] message) {
        initialiseIV(iv);
        decrypt( message );
    }

    @Override
    public String getStateString(StringOutputFormatting formatting) {
        StringBuilder string = new StringBuilder();

        switch (formatting)
        {
            case PLAIN:
                for (int xj : x) {
                    string.append(String.format("%08X ", xj));
                }

                for (int cj : c) {
                    string.append(String.format("%08X ", cj));
                }

                string.append(b);
                break;

            case FANCY:
                string.append("b = " + b);

                for (int j=0; j<8; j++) {
                    if (j % 4 == 0) string.append("\n");
                    else string.append(" ");
                    string.append("X"+ j + " = " + String.format("0x%08X", x[j]) + ",");
                }
                for (int j=0; j<8; j++) {
                    if (j % 4 == 0) string.append("\n");
                    else string.append(" ");
                    string.append("C"+ j + " = " + String.format("0x%08X", c[j]));
                    if (j != 7) string.append(",");
                }
        }


        return string.toString();
    }

    private int rotatel(int x, int n) {
        return (x << n) | (x >>> (32 - n));
    }

    private int toBytePairInt(byte x, byte y) {
        return (x << 8 | y & 0xFF);
    }


}

