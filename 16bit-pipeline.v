

// Behavioral implementation of MIPS Register File (modified to 16 bit reg width over 4 regs)
module reg_file (RR1,RR2,WR,WD,RegWrite,RD1,RD2,clock);

  input [1:0] RR1,RR2,WR;
  input [15:0] WD;
  input RegWrite,clock;
  output [15:0] RD1,RD2;

  reg [15:0] Regs[0:3];

  assign RD1 = Regs[RR1];
  assign RD2 = Regs[RR2];

  initial Regs[0] = 0;

  always @(negedge clock)
    if (RegWrite==1 & WR!=0) 
	Regs[WR] <= WD;

endmodule

//gate level half adder
module halfadder (S,C,x,y);
   input x,y;
   output S,C;
   
   xor (S,x,y);
   and (C,x,y);
endmodule

//gate level full adder
module fulladder (S,C,x,y,z);
   input x,y,z;
   output S,C;
   wire S1,D1,D2; 
    halfadder HA1 (S1,D1,x,y),
              HA2 (S,D2,S1,z);
    or g1(C,D2,D1);
endmodule

//2 to 1 multiplexer
//choose x on z=0, y on z=1
module two_bit_multiplex(x, y, z, O);
    input x, y, z;
    output O;
    not n1(z1, z);
    and a1(S1, x, y),
       a2(S2, y, z),
       a3(S3, x, z1);
    or(O, S1, S2, S3);
endmodule

//16 bit wide 2 to 1 multiplexer
module two_to_one_sixteen_bit_mux(x, y, z, O);
    input [15:0] x, y;
    input z;
    output [15:0] O;
    two_bit_multiplex mux0 (x[0], y[0], z, O[0]),
                      mux1 (x[1], y[1], z, O[1]),
                      mux2 (x[2], y[2], z, O[2]),
                      mux3 (x[3], y[3], z, O[3]),
                      mux4 (x[4], y[4], z, O[4]),
                      mux5 (x[5], y[5], z, O[5]),
                      mux6 (x[6], y[6], z, O[6]),
                      mux7 (x[7], y[7], z, O[7]),
                      mux8 (x[8], y[8], z, O[8]),
                      mux9 (x[9], y[9], z, O[9]),
                      mux10 (x[10], y[10], z, O[10]),
                      mux11 (x[11], y[11], z, O[11]),
                      mux12 (x[12], y[12], z, O[12]),
                      mux13 (x[13], y[13], z, O[13]),
                      mux14 (x[14], y[14], z, O[14]),
                      mux15 (x[15], y[15], z, O[15]);
endmodule

//2 bit wide 2 to 1 multiplexer
module two_to_one_two_bit_mux(x, y, z, O);
    input [1:0] x, y;
    input z;
    output [1:0] O;
    two_bit_multiplex mux0 (x[0], y[0], z, O[0]),
                      mux1 (x[1], y[1], z, O[1]);
endmodule

//4 to 1 multiplexer
module four_bit_multiplex(A, B, C, D, ctrl1, ctrl2, O);
    input A, B, C, D, ctrl1, ctrl2;
    output O;
    two_bit_multiplex m1(A, B, ctrl1, tmp),
                      m2(C, D, ctrl1, tmp1),
                      m3(tmp, tmp1, ctrl2, O);
endmodule

//alu module for all but the most significant bit
module one_bit_ALU(A, B, bnot, anot, less, carryIn, ctrl2, ctrl1, out, Cout);
    input A, B, bnot, anot, less, carryIn, ctrl1, ctrl2;
    output out, Cout;
    
    not n1(nA, A),
        n2(nB, B);
        
    two_bit_multiplex mA(A, nA, anot, uA),
                      mB(B, nB, bnot, uB);
    
    and a1(BandA, uA, uB);
    or  o1(BorA, uA, uB);
    
    fulladder adder(S, Cout, uA, uB, carryIn);
    
    four_bit_multiplex m1(BandA, BorA, S, less, ctrl1, ctrl2, out);
endmodule

//alu module for the most significant bit
module one_bit_ALU2(A, B, bnot, anot, set, carryIn, ctrl2, ctrl1, out, Cout);
    input A, B, bnot, anot, carryIn, ctrl1, ctrl2;
    output out, Cout, set;
    
    not n1(nA, A),
        n2(nB, B);
        
    two_bit_multiplex mA(A, nA, anot, uA),
                      mB(B, nB, bnot, uB);
    
    and a1(BandA, uA, uB);
    or  o1(BorA, uA, uB);
    
    fulladder adder(S, Cout, uA, uB, carryIn);
    and(set, S, 1);
    
    four_bit_multiplex m1(BandA, BorA, S, 1'b0, ctrl1, ctrl2, out);
endmodule

//16 bit arithmetic logic unit
module alu(op, a, b, result, zero);
    input[3:0] op;
    input [15:0] a, b;
    output[15:0] result;
    output zero;
    
   one_bit_ALU a1 (a[0], b[0], op[2], op[3], set, op[2], op[1], op[0], result[0], Carry1);
   one_bit_ALU a2 (a[1], b[1], op[2], op[3], 1'b0, Carry1, op[1], op[0], result[1], Carry2);
   one_bit_ALU a3 (a[2], b[2], op[2], op[3], 1'b0, Carry2, op[1], op[0], result[2], Carry3);
   one_bit_ALU a4 (a[3], b[3], op[2], op[3], 1'b0, Carry3, op[1], op[0], result[3], Carry4);
   one_bit_ALU a5 (a[4], b[4], op[2], op[3], 1'b0, Carry4, op[1], op[0], result[4], Carry5);
   one_bit_ALU a6 (a[5], b[5], op[2], op[3], 1'b0, Carry5, op[1], op[0], result[5], Carry6);
   one_bit_ALU a7 (a[6], b[6], op[2], op[3], 1'b0, Carry6, op[1], op[0], result[6], Carry7);
   one_bit_ALU a8 (a[7], b[7], op[2], op[3], 1'b0, Carry7, op[1], op[0], result[7], Carry8);
   one_bit_ALU a9 (a[8], b[8], op[2], op[3], 1'b0, Carry8, op[1], op[0], result[8], Carry9);
   one_bit_ALU a10 (a[9], b[9], op[2], op[3], 1'b0, Carry9, op[1], op[0], result[9], Carry10);
   one_bit_ALU a11 (a[10], b[10], op[2], op[3], 1'b0, Carry10, op[1], op[0], result[10], Carry11);
   one_bit_ALU a12 (a[11], b[11], op[2], op[3], 1'b0, Carry11, op[1], op[0], result[11], Carry12);
   one_bit_ALU a13 (a[12], b[12], op[2], op[3], 1'b0, Carry12, op[1], op[0], result[12], Carry13);
   one_bit_ALU a14 (a[13], b[13], op[2], op[3], 1'b0, Carry13, op[1], op[0], result[13], Carry14);
   one_bit_ALU a15 (a[14], b[14], op[2], op[3], 1'b0, Carry14, op[1], op[0], result[14], Carry15);
   one_bit_ALU2 a16 (a[15], b[15], op[2], op[3], set, Carry15, op[1], op[0], result[15], Cout);
   
   xor(o1, Carry3, Cout);
   nor(zero, result[0], result[1], result[2], result[3], result[4], result[5], result[6], result[7], result[8], result[9], result[10], result[11], result[12], result[13], result[14], result[15]);
   
endmodule


//main control unit for interpretting opcodes into control signals for the rest of the CPU
module MainControl (Op,Control); 
  input [3:0] Op;
  output reg [10:0] Control;
// Control bits: RegDst,ALUSrc, RegWrite, MemToReg, MemWrite, bne, beq, ALUOp
  always @(Op) case (Op)
    4'b0010: Control <= 11'b101_00_00_0000; // AND
    4'b0111: Control <= 11'b011_00_00_0010; // ADDI
    4'b0000: Control <= 11'b101_00_00_0010; //ADD
    4'b0001: Control <= 11'b101_00_00_0110; //SUB
    4'b0011: Control <= 11'b101_00_00_0001; //OR
    4'b0100: Control <= 11'b101_00_00_1100; //NOR
    4'b0101: Control <= 11'b101_00_00_1101; //NAND
    4'b0110: Control <= 11'b101_00_00_0111; //SLT
    4'b1000: Control <= 11'b011_10_00_0010; //LW
    4'b1001: Control <= 11'b010_01_00_0010; //SW
    4'b1010: Control <= 11'b000_00_01_0110;//BEQ
    4'b1011: Control <= 11'b000_00_10_0110;//BNE
    
    
  endcase
endmodule

//gate level branching logic
module BranchControl (Beq, Bne, Zero, BranchCtrl);
    input Beq, Bne, Zero;
    output BranchCtrl;
    and beqand (beqtrue, Beq, Zero),
        bneand (bnetrue, Bne, ~Zero);
    or (BranchCtrl, beqtrue, bnetrue);
endmodule

//Overall CPU
module CPU (clock,PC,IFID_IR,IDEX_IR,EXMEM_IR,MEMWB_IR,WD);
  input clock;
  output [15:0] PC,IFID_IR,IDEX_IR,EXMEM_IR,MEMWB_IR,WD;

  initial begin 
// Program: swap memory cells (if needed) and compute absolute value |5-7|=2
   IMemory[0] = 16'b1000_00_01_00000000;  // lw $t1, 0($0) 
   IMemory[1] = 16'b1000_00_10_00000010;  // lw $t2, 4($0)
   IMemory[2] = 16'h0000;  // nop
   IMemory[3]  = 16'h0000;  // nop
   IMemory[4]  = 16'h0000;  // nop
   IMemory[5] = 16'b0110_01_10_11_000000;  // slt $t3, $t1, $t2
   IMemory[6]  = 16'h0;  // nop
   IMemory[7]  = 16'h0;  // nop
   IMemory[8]  = 16'h0;  // nop
   IMemory[9] = 16'b1010_11_00_00001000;  // beq $t3, $0, IMemory[15]
   IMemory[10] = 16'h0;  // nop
   IMemory[11] = 16'h0;  // nop
   IMemory[12] = 26'h0;  // nop
   IMemory[13] = 16'b1001_00_01_00000100;  // sw $t1, 4($0) 
   IMemory[14] = 16'b1001_00_10_00000000;  // sw $t2, 0($0) 
   IMemory[15] = 16'h0;  // nop
   IMemory[16] = 16'h0;  // nop
   IMemory[17] = 16'h0;  // nop
   IMemory[18] = 16'b1000_00_01_00000000;  // lw $t1, 0($0) 
   IMemory[19] = 16'b1000_00_10_00000100;  // lw $t2, 4($0) 
   IMemory[20] = 16'h0;  // nop
   IMemory[21] = 16'h0;  // nop
   IMemory[22] = 16'h0;  // nop
   IMemory[23] = 16'b0100_10_10_10_000000;  // nor $t2, $t2, $t2 (sub $3, $1, $2 in two's complement)
   IMemory[24] = 16'h0;  // nop
   IMemory[25] = 16'h0;  // nop
   IMemory[26] = 16'h0;  // nop
   IMemory[27] = 16'b0111_10_10_00000001;  // addi $t2, $t2, 1 
   IMemory[28] = 16'h0;  // nop
   IMemory[29] = 16'h0;  // nop
   IMemory[30] = 16'h0;  // nop
   IMemory[31] = 16'b0000_01_10_11_000000;  // add $t3, $t1, $t2
 
// Data
   DMemory[0] = 5; // switch the cells and see how the simulation output changes
   DMemory[1] = 7; // (beq is taken if DMemory[0]=7; DMemory[1]=5, not taken otherwise)
  end

// Pipeline 
// IF 
   wire [15:0] PCplus4, NextPC;
   reg[15:0] PC, IMemory[0:1023], IFID_IR, IFID_PCplus4;
   alu fetch (4'b0010,PC,16'b0010,PCplus4,Unused1);
   //assign NextPC = (EXMEM_beq && EXMEM_Zero) || (EXMEM_bne && !EXMEM_Zero) ? EXMEM_Target: PCplus4;
   
   two_to_one_sixteen_bit_mux nextPCmux (PCplus4, EXMEM_Target, (EXMEM_beq && EXMEM_Zero) || (EXMEM_bne && !EXMEM_Zero), NextPC);
// ID
   wire [10:0] Control;
   reg IDEX_RegWrite,IDEX_MemtoReg,
       IDEX_Branch,  IDEX_MemWrite,
       IDEX_ALUSrc,  IDEX_RegDst,
       IDEX_bne,     IDEX_beq;
   
   reg [3:0] IDEX_ALUctl;
   wire [15:0] RD1,RD2,SignExtend, WD;
   reg [15:0] IDEX_PCplus4,IDEX_RD1,IDEX_RD2,IDEX_SignExt,IDEXE_IR;
   reg [15:0] IDEX_IR; // For monitoring the pipeline
   reg [1:0]  IDEX_rt,IDEX_rd;
   reg MEMWB_RegWrite; // part of MEM stage, but declared here before use (to avoid error)
   reg [1:0] MEMWB_rd; // part of MEM stage, but declared here before use (to avoid error)
   //module reg_file (RR1,RR2,WR,WD,RegWrite,RD1,RD2,clock);
   reg_file rf (IFID_IR[11:10],IFID_IR[9:8],MEMWB_rd,WD,MEMWB_RegWrite,RD1,RD2,clock);
   MainControl MainCtr (IFID_IR[15:12],Control); 
   assign SignExtend = {{8{IFID_IR[7]}},IFID_IR[7:0]}; 
// EXE
   reg EXMEM_RegWrite,EXMEM_MemtoReg,
       EXMEM_bne, EXMEM_beq, EXMEM_MemWrite;
   wire [15:0] Target;
   reg EXMEM_Zero;
   reg [15:0] EXMEM_Target,EXMEM_ALUOut,EXMEM_RD2;
   reg [15:0] EXMEM_IR; // For monitoring the pipeline
   reg [1:0] EXMEM_rd;
   wire [15:0] B,ALUOut;
   wire [3:0] ALUctl;
   wire [1:0] WR;
   alu branch (4'b0010,IDEX_SignExt<<1,IDEX_PCplus4,Target,Unused2);
   alu ex (IDEX_ALUctl, IDEX_RD1, B, ALUOut, Zero);
   //ALUControl ALUCtrl(IDEX_ALUOp, IDEX_SignExt[5:0], ALUctl); // ALU control unit
   //assign B  = (IDEX_ALUSrc) ? IDEX_SignExt: IDEX_RD2;        // ALUSrc Mux
   two_to_one_sixteen_bit_mux ALUSrcmux (IDEX_RD2, IDEX_SignExt, IDEX_ALUSrc, B);
   //assign WR = (IDEX_RegDst) ? IDEX_rd: IDEX_rt;              // RegDst Mux
   two_to_one_two_bit_mux RegDstmux (IDEX_rt, IDEX_rd, IDEX_RegDst, WR);
// MEM
   reg MEMWB_MemtoReg;
   reg [15:0] DMemory[0:1023],MEMWB_MemOut,MEMWB_ALUOut;
   reg [15:0] MEMWB_IR; // For monitoring the pipeline
   wire [15:0] MemOut;
   assign MemOut = DMemory[EXMEM_ALUOut>>1];
   always @(negedge clock) if (EXMEM_MemWrite) DMemory[EXMEM_ALUOut>>1] <= EXMEM_RD2;
// WB
   assign WD = (MEMWB_MemtoReg) ? MEMWB_MemOut: MEMWB_ALUOut; // MemtoReg Mux
   two_to_one_sixteen_bit_mux MemtoRegmux (MEMWB_ALUOut, MEMWB_MemOut, MEMWB_MemtoReg, WD);

   initial begin
    PC = 0;
// Initialize pipeline registers
    IDEX_RegWrite=0;IDEX_MemtoReg=0;IDEX_bne=0; IDEX_beq = 0;IDEX_MemWrite=0;IDEX_ALUSrc=0;IDEX_RegDst=0;IDEX_ALUctl=0;
    IFID_IR=0;
    EXMEM_RegWrite=0;EXMEM_MemtoReg=0;EXMEM_bne=0; EXMEM_beq = 0;EXMEM_MemWrite=0;
    EXMEM_Target=0;
    MEMWB_RegWrite=0;MEMWB_MemtoReg=0;
   end

// Running the pipeline
   always @(negedge clock) begin 
// IF
    PC <= NextPC;
    IFID_PCplus4 <= PCplus4;
    IFID_IR <= IMemory[PC>>1];
// ID
    IDEX_IR <= IFID_IR; // For monitoring the pipeline
    // Control bits: RegDst,ALUSrc, RegWrite, MemToReg, MemWrite, bne, beq, ALUOp
    {IDEX_RegDst,IDEX_ALUSrc,IDEX_RegWrite,IDEX_MemtoReg, IDEX_MemWrite,IDEX_bne, IDEX_beq,IDEX_ALUctl} <= Control;  
    //ALUctl <= IDEX_ALUctl;
    IDEX_PCplus4 <= IFID_PCplus4;
    IDEX_RD1 <= RD1; 
    IDEX_RD2 <= RD2;
    IDEX_SignExt <= SignExtend;
    IDEX_rt <= IFID_IR[9:8];
    IDEX_rd <= IFID_IR[7:6];
// EXE
    EXMEM_IR <= IDEX_IR; // For monitoring the pipeline
    EXMEM_RegWrite <= IDEX_RegWrite;
    EXMEM_MemtoReg <= IDEX_MemtoReg;
    EXMEM_bne   <= IDEX_bne;
    EXMEM_beq   <= IDEX_beq;
    EXMEM_MemWrite <= IDEX_MemWrite;
    EXMEM_Target <= Target;
    EXMEM_Zero <= Zero;
    EXMEM_ALUOut <= ALUOut;
    EXMEM_RD2 <= IDEX_RD2;
    EXMEM_rd <= WR;
// MEM
    MEMWB_IR <= EXMEM_IR; // For monitoring the pipeline
    MEMWB_RegWrite <= EXMEM_RegWrite;
    MEMWB_MemtoReg <= EXMEM_MemtoReg;
    MEMWB_MemOut <= MemOut;
    MEMWB_ALUOut <= EXMEM_ALUOut;
    MEMWB_rd <= EXMEM_rd;
// WB
// Register write happens on neg edge of the clock (if MEMWB_RegWrite is asserted)   
   // $display("%b", ALUOut);
  end
endmodule

// Test module
module test ();
  reg clock;
  wire signed [15:0] PC,IFID_IR,IDEX_IR,EXMEM_IR,MEMWB_IR,WD;
  CPU test_cpu(clock,PC,IFID_IR,IDEX_IR,EXMEM_IR,MEMWB_IR,WD);
  always #1 clock = ~clock;
  initial begin
    $display ("PC   IFID_IR        IDEX_IR        EXMEM_IR       MEMWB_IR        WD");
    $monitor ("%3d  %b %b %b %b %2d",PC,IFID_IR,IDEX_IR,EXMEM_IR,MEMWB_IR,WD);
    clock = 1;
    #69 $finish;
  end
endmodule

/* Output:
PC   IFID_IR  IDEX_IR  EXMEM_IR MEMWB_IR  WD
  0  00000000 xxxxxxxx xxxxxxxx xxxxxxxx  x
  4  8c090000 00000000 xxxxxxxx xxxxxxxx  x
  8  8c0a0004 8c090000 00000000 xxxxxxxx  x
 12  00000000 8c0a0004 8c090000 00000000  0
 16  00000000 00000000 8c0a0004 8c090000  5
 20  00000000 00000000 00000000 8c0a0004  7
 24  012a582a 00000000 00000000 00000000  0
 28  00000000 012a582a 00000000 00000000  0
 32  00000000 00000000 012a582a 00000000  0
 36  00000000 00000000 00000000 012a582a  1
 40  11600005 00000000 00000000 00000000  0
 44  00000000 11600005 00000000 00000000  0
 48  00000000 00000000 11600005 00000000  0
 52  00000000 00000000 00000000 11600005  1
 56  ac090004 00000000 00000000 00000000  0
 60  ac0a0000 ac090004 00000000 00000000  0
 64  00000000 ac0a0000 ac090004 00000000  0
 68  00000000 00000000 ac0a0000 ac090004  4
 72  00000000 00000000 00000000 ac0a0000  0
 76  8c090000 00000000 00000000 00000000  0
 80  8c0a0004 8c090000 00000000 00000000  0
 84  00000000 8c0a0004 8c090000 00000000  0
 88  00000000 00000000 8c0a0004 8c090000  7
 92  00000000 00000000 00000000 8c0a0004  5
 96  014a5027 00000000 00000000 00000000  0
100  00000000 014a5027 00000000 00000000  0
104  00000000 00000000 014a5027 00000000  0
108  00000000 00000000 00000000 014a5027 -6
112  214a0001 00000000 00000000 00000000 -1
116  00000000 214a0001 00000000 00000000 -1
120  00000000 00000000 214a0001 00000000 -1
124  00000000 00000000 00000000 214a0001 -5
128  012a5820 00000000 00000000 00000000  0
132  xxxxxxxx 012a5820 00000000 00000000  0
136  xxxxxxxx xxxxxxxx 012a5820 00000000  0
140  xxxxxxxx xxxxxxxx xxxxxxxx 012a5820  2
*/

