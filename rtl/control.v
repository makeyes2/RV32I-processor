
// =============================================================================
// Control Signal Truth Table
// =============================================================================
// Instruction Type       | Opcode  | Branch | MemRead | MemtoReg | MemWrite | ALUSrc | RegWrite
// -----------------------|---------|--------|---------|----------|----------|--------|----------
// R-type (add, sub, etc.)| 0110011 |   0    |    0    |    0     |    0     |   0    |    1
// I-type (addi, etc.)    | 0010011 |   0    |    0    |    0     |    0     |   1    |    1
// Load (lw, lh, lb, etc.)| 0000011 |   0    |    1    |    1     |    0     |   1    |    1
// Store (sw, sh, sb)     | 0100011 |   0    |    0    |    X     |    1     |   1    |    0
// Branch (beq, bne, etc.)| 1100011 |   1    |    0    |    X     |    0     |   0    |    0
// =============================================================================

module ctl (
    input wire [ 6:0 ] instruction,

    output wire [ 1:0 ] U_sel,
    output wire [ 5:0 ] i_format,
    output wire [ 2:0 ] bj_type,
    output wire [ 5:0 ] alu_op,
    output wire mem_read,
    output wire mem_to_reg,
    output wire mem_write,
    output wire alu_src,
    output wire reg_write
);

    // Decode opcode
    wire [6:0] opcode = instruction[6:0];

    // Opcode definitions
    localparam OP_RTYPE  = 7'b0110011;  // R-type arithmetic
    localparam OP_ITYPE  = 7'b0010011;  // I-type arithmetic
    localparam OP_LOAD   = 7'b0000011;  // Load instructions
    localparam OP_STORE  = 7'b0100011;  // Store instructions
    localparam OP_BRANCH = 7'b1100011;  // Branch instructions
    localparam OP_JAL    = 7'b1101111;  // JAL
    localparam OP_JALR   = 7'b1100111;  // JALR
    localparam OP_LUI    = 7'b0110111;  // LUI
    localparam OP_AUIPC  = 7'b0010111;  // AUIPC

    // Branch/Jump type definitions
    localparam BJ_NONE   = 3'b000;
    localparam BJ_BEQ    = 3'b001;
    localparam BJ_BNE    = 3'b010;
    localparam BJ_BLT    = 3'b011;
    localparam BJ_BGE    = 3'b100;
    localparam BJ_BLTU   = 3'b101;
    localparam BJ_BGEU   = 3'b110;
    localparam BJ_JAL    = 3'b001;  // JAL uses bj_type for jump type
    localparam BJ_JALR   = 3'b010;  // JALR uses bj_type for jump type

    // U_sel definitions (for LUI/AUIPC)
    localparam U_NONE    = 2'b00;
    localparam U_LUI     = 2'b01;
    localparam U_AUIPC   = 2'b10;

    // Format encoding (one-hot): [5]=J, [4]=U, [3]=B, [2]=S, [1]=I, [0]=R
    reg [5:0] format;
    reg [2:0] branch_jump;
    reg [1:0] u_select;
    reg [5:0] alu_operation;
    reg       mem_rd, mem_to_r, mem_wr, alu_s, reg_wr;

    always @(*) begin
        // Default values
        format = 6'b000001;  // Default to R-type
        branch_jump = BJ_NONE;
        u_select = U_NONE;
        alu_operation = 6'b000001;  // Default ALU operation
        mem_rd = 1'b0;
        mem_to_r = 1'b0;
        mem_wr = 1'b0;
        alu_s = 1'b0;
        reg_wr = 1'b0;

        case (opcode)
            OP_RTYPE: begin  // R-type (add, sub, and, or, xor, sll, srl, sra, slt, sltu)
                format = 6'b000001;    // R-type format
                branch_jump = BJ_NONE;
                mem_rd = 1'b0;
                mem_to_r = 1'b0;
                mem_wr = 1'b0;
                alu_s = 1'b0;          // Use rs2 (not immediate)
                reg_wr = 1'b1;         // Write to rd
                alu_operation = 6'b000001;
            end

            OP_ITYPE: begin  // I-type arithmetic (addi, slti, sltiu, xori, ori, andi, slli, srli, srai)
                format = 6'b000010;    // I-type format
                branch_jump = BJ_NONE;
                mem_rd = 1'b0;
                mem_to_r = 1'b0;
                mem_wr = 1'b0;
                alu_s = 1'b1;          // Use immediate
                reg_wr = 1'b1;         // Write to rd
                alu_operation = 6'b000010;
            end

            OP_LOAD: begin  // Load (lb, lh, lw, lbu, lhu)
                format = 6'b000010;    // I-type format
                branch_jump = BJ_NONE;
                mem_rd = 1'b1;         // Read from memory
                mem_to_r = 1'b1;       // Write memory data to register
                mem_wr = 1'b0;
                alu_s = 1'b1;          // Use immediate for address calculation
                reg_wr = 1'b1;         // Write to rd
                alu_operation = 6'b000010;
            end

            OP_STORE: begin  // Store (sb, sh, sw)
                format = 6'b000100;    // S-type format
                branch_jump = BJ_NONE;
                mem_rd = 1'b0;
                mem_to_r = 1'b0;       // Don't care
                mem_wr = 1'b1;         // Write to memory
                alu_s = 1'b1;          // Use immediate for address calculation
                reg_wr = 1'b0;         // Don't write to register
                alu_operation = 6'b000100;
            end

            OP_BRANCH: begin  // Branch (beq, bne, blt, bge, bltu, bgeu)
                format = 6'b001000;    // B-type format
                case (instruction[14:12])  // funct3
                    3'b000: branch_jump = BJ_BEQ;   // beq
                    3'b001: branch_jump = BJ_BNE;   // bne
                    3'b100: branch_jump = BJ_BLT;   // blt
                    3'b101: branch_jump = BJ_BGE;   // bge
                    3'b110: branch_jump = BJ_BLTU;  // bltu
                    3'b111: branch_jump = BJ_BGEU;  // bgeu
                    default: branch_jump = BJ_NONE;
                endcase
                mem_rd = 1'b0;
                mem_to_r = 1'b0;       // Don't care
                mem_wr = 1'b0;
                alu_s = 1'b0;          // Compare rs1 and rs2
                reg_wr = 1'b0;         // Don't write to register
                alu_operation = 6'b001000;
            end

            OP_JAL: begin  // JAL
                format = 6'b100000;    // J-type format
                branch_jump = BJ_JAL;
                mem_rd = 1'b0;
                mem_to_r = 1'b0;
                mem_wr = 1'b0;
                alu_s = 1'b0;          // Don't care
                reg_wr = 1'b1;         // Write PC+4 to rd
                alu_operation = 6'b100000;
            end

            OP_JALR: begin  // JALR
                format = 6'b000010;    // I-type format
                branch_jump = BJ_JALR;
                mem_rd = 1'b0;
                mem_to_r = 1'b0;
                mem_wr = 1'b0;
                alu_s = 1'b1;          // Use immediate
                reg_wr = 1'b1;         // Write PC+4 to rd
                alu_operation = 6'b000010;
            end

            OP_LUI: begin  // LUI
                format = 6'b010000;    // U-type format
                branch_jump = BJ_NONE;
                u_select = U_LUI;
                mem_rd = 1'b0;
                mem_to_r = 1'b0;
                mem_wr = 1'b0;
                alu_s = 1'b0;          // Don't care
                reg_wr = 1'b1;         // Write immediate to rd
                alu_operation = 6'b010000;
            end

            OP_AUIPC: begin  // AUIPC
                format = 6'b010000;    // U-type format
                branch_jump = BJ_NONE;
                u_select = U_AUIPC;
                mem_rd = 1'b0;
                mem_to_r = 1'b0;
                mem_wr = 1'b0;
                alu_s = 1'b0;          // Don't care
                reg_wr = 1'b1;         // Write PC + immediate to rd
                alu_operation = 6'b010000;
            end

            default: begin  // Invalid opcode
                format = 6'b000000;
                branch_jump = BJ_NONE;
                u_select = U_NONE;
                mem_rd = 1'b0;
                mem_to_r = 1'b0;
                mem_wr = 1'b0;
                alu_s = 1'b0;
                reg_wr = 1'b0;
                alu_operation = 6'b000000;
            end
        endcase
    end

    // Assign outputs
    assign i_format = format;
    assign bj_type = branch_jump;
    assign U_sel = u_select;
    assign alu_op = alu_operation;
    assign mem_read = mem_rd;
    assign mem_to_reg = mem_to_r;
    assign mem_write = mem_wr;
    assign alu_src = alu_s;
    assign reg_write = reg_wr;

endmodule