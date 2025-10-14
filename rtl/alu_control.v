module alu_ctl(
  input wire [ 5:0 ] alu_op,
  input wire [ 31:0 ] instruction,

  output wire [ 2:0 ] i_opsel,
  output wire i_sub,
  output wire i_unsigned,
  output wire i_arith
);

    // Extract funct3 and funct7 fields from instruction
    wire [2:0] funct3 = instruction[14:12];
    wire [6:0] funct7 = instruction[31:25];
    wire       funct7_bit5 = instruction[30];  // Distinguishes SUB from ADD, SRA from SRL

    // ALU operation encoding from control unit (one-hot)
    wire is_rtype  = alu_op[0];  // R-type ALU operations
    wire is_itype  = alu_op[1];  // I-type ALU operations
    wire is_store  = alu_op[2];  // Store (address calculation)
    wire is_branch = alu_op[3];  // Branch comparison
    wire is_utype  = alu_op[4];  // U-type (LUI/AUIPC)
    wire is_jtype  = alu_op[5];  // J-type (JAL/JALR)

    // ALU opsel values (corresponds to alu.v):
    // 3'b000: ADD/SUB (controlled by i_sub)
    // 3'b001: SLL (shift left logical)
    // 3'b010/3'b011: SLT/SLTU (set less than, controlled by i_unsigned)
    // 3'b100: XOR
    // 3'b101: SRL/SRA (shift right logical/arithmetic, controlled by i_arith)
    // 3'b110: OR
    // 3'b111: AND

    reg [2:0] opsel;
    reg       sub;
    reg       unsign;
    reg       arith;

    always @(*) begin
        // Default values
        opsel = 3'b000;   // Default to ADD
        sub = 1'b0;
        unsign = 1'b0;
        arith = 1'b0;

        // For load/store instructions, always ADD for address calculation
        if (is_store) begin
            opsel = 3'b000;   // ADD
            sub = 1'b0;
            unsign = 1'b0;
            arith = 1'b0;
        end
        // For R-type and I-type ALU operations
        else if (is_rtype || is_itype) begin
            case (funct3)
                3'b000: begin  // ADD/SUB (R-type) or ADDI (I-type)
                    opsel = 3'b000;
                    sub = is_rtype && funct7_bit5;  // SUB only in R-type with funct7[5]=1
                    unsign = 1'b0;
                    arith = 1'b0;
                end
                3'b001: begin  // SLL/SLLI (shift left logical)
                    opsel = 3'b001;
                    sub = 1'b0;
                    unsign = 1'b0;
                    arith = 1'b0;
                end
                3'b010: begin  // SLT/SLTI (set less than signed)
                    opsel = 3'b010;
                    sub = 1'b0;
                    unsign = 1'b0;
                    arith = 1'b0;
                end
                3'b011: begin  // SLTU/SLTIU (set less than unsigned)
                    opsel = 3'b011;
                    sub = 1'b0;
                    unsign = 1'b1;
                    arith = 1'b0;
                end
                3'b100: begin  // XOR/XORI
                    opsel = 3'b100;
                    sub = 1'b0;
                    unsign = 1'b0;
                    arith = 1'b0;
                end
                3'b101: begin  // SRL/SRLI or SRA/SRAI (shift right)
                    opsel = 3'b101;
                    sub = 1'b0;
                    unsign = 1'b0;
                    arith = funct7_bit5;  // Arithmetic if funct7[5]=1 (SRA/SRAI)
                end
                3'b110: begin  // OR/ORI
                    opsel = 3'b110;
                    sub = 1'b0;
                    unsign = 1'b0;
                    arith = 1'b0;
                end
                3'b111: begin  // AND/ANDI
                    opsel = 3'b111;
                    sub = 1'b0;
                    unsign = 1'b0;
                    arith = 1'b0;
                end
            endcase
        end
        // For branch operations, use SUB for comparison
        else if (is_branch) begin
            opsel = 3'b000;   // ADD (but will use for comparison)
            sub = 1'b1;       // Subtract for comparison
            // Unsigned comparison for BLTU/BGEU
            unsign = (funct3 == 3'b110) || (funct3 == 3'b111);
            arith = 1'b0;
        end
        // For other operations (JAL, JALR, LUI, AUIPC), use ADD
        else begin
            opsel = 3'b000;
            sub = 1'b0;
            unsign = 1'b0;
            arith = 1'b0;
        end
    end

    // Output assignments
    assign i_opsel = opsel;
    assign i_sub = sub;
    assign i_unsigned = unsign;
    assign i_arith = arith;

endmodule