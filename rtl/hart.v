module hart #(
    // After reset, the program counter (PC) should be initialized to this
    // address and start executing instructions from there.
    parameter RESET_ADDR = 32'h00000000
) (
    // Global clock.
    input  wire        i_clk,
    // Synchronous active-high reset.
    input  wire        i_rst,
    // Instruction fetch goes through a read only instruction memory (imem)
    // port. The port accepts a 32-bit address (e.g. from the program counter)
    // per cycle and combinationally returns a 32-bit instruction word. This
    // is not representative of a realistic memory interface; it has been
    // modeled as more similar to a DFF or SRAM to simplify phase 3. In
    // later phases, you will replace this with a more realistic memory.
    //
    // 32-bit read address for the instruction memory. This is expected to be
    // 4 byte aligned - that is, the two LSBs should be zero.
    output wire [31:0] o_imem_raddr,
    // Instruction word fetched from memory, available on the same cycle.
    input  wire [31:0] i_imem_rdata,
    // Data memory accesses go through a separate read/write data memory (dmem)
    // that is shared between read (load) and write (stored). The port accepts
    // a 32-bit address, read or write enable, and mask (explained below) each
    // cycle. Reads are combinational - values are available immediately after
    // updating the address and asserting read enable. Writes occur on (and
    // are visible at) the next clock edge.
    //
    // Read/write address for the data memory. This should be 32-bit aligned
    // (i.e. the two LSB should be zero). See `o_dmem_mask` for how to perform
    // half-word and byte accesses at unaligned addresses.
    output wire [31:0] o_dmem_addr,
    // When asserted, the memory will perform a read at the aligned address
    // specified by `i_addr` and return the 32-bit word at that address
    // immediately (i.e. combinationally). It is illegal to assert this and
    // `o_dmem_wen` on the same cycle.
    output wire        o_dmem_ren,
    // When asserted, the memory will perform a write to the aligned address
    // `o_dmem_addr`. When asserted, the memory will write the bytes in
    // `o_dmem_wdata` (specified by the mask) to memory at the specified
    // address on the next rising clock edge. It is illegal to assert this and
    // `o_dmem_ren` on the same cycle.
    output wire        o_dmem_wen,
    // The 32-bit word to write to memory when `o_dmem_wen` is asserted. When
    // write enable is asserted, the byte lanes specified by the mask will be
    // written to the memory word at the aligned address at the next rising
    // clock edge. The other byte lanes of the word will be unaffected.
    output wire [31:0] o_dmem_wdata,
    // The dmem interface expects word (32 bit) aligned addresses. However,
    // WISC-25 supports byte and half-word loads and stores at unaligned and
    // 16-bit aligned addresses, respectively. To support this, the access
    // mask specifies which bytes within the 32-bit word are actually read
    // from or written to memory.
    //
    // To perform a half-word read at address 0x00001002, align `o_dmem_addr`
    // to 0x00001000, assert `o_dmem_ren`, and set the mask to 0b1100 to
    // indicate that only the upper two bytes should be read. Only the upper
    // two bytes of `i_dmem_rdata` can be assumed to have valid data; to
    // calculate the final value of the `lh[u]` instruction, shift the rdata
    // word right by 16 bits and sign/zero extend as appropriate.
    //
    // To perform a byte write at address 0x00002003, align `o_dmem_addr` to
    // `0x00002003`, assert `o_dmem_wen`, and set the mask to 0b1000 to
    // indicate that only the upper byte should be written. On the next clock
    // cycle, the upper byte of `o_dmem_wdata` will be written to memory, with
    // the other three bytes of the aligned word unaffected. Remember to shift
    // the value of the `sb` instruction left by 24 bits to place it in the
    // appropriate byte lane.
    output wire [ 3:0] o_dmem_mask,
    // The 32-bit word read from data memory. When `o_dmem_ren` is asserted,
    // this will immediately reflect the contents of memory at the specified
    // address, for the bytes enabled by the mask. When read enable is not
    // asserted, or for bytes not set in the mask, the value is undefined.
    input  wire [31:0] i_dmem_rdata,
	// The output `retire` interface is used to signal to the testbench that
    // the CPU has completed and retired an instruction. A single cycle
    // implementation will assert this every cycle; however, a pipelined
    // implementation that needs to stall (due to internal hazards or waiting
    // on memory accesses) will not assert the signal on cycles where the
    // instruction in the writeback stage is not retiring.
    //
    // Asserted when an instruction is being retired this cycle. If this is
    // not asserted, the other retire signals are ignored and may be left invalid.
    output wire        o_retire_valid,
    // The 32 bit instruction word of the instrution being retired. This
    // should be the unmodified instruction word fetched from instruction
    // memory.
    output wire [31:0] o_retire_inst,
    // Asserted if the instruction produced a trap, due to an illegal
    // instruction, unaligned data memory access, or unaligned instruction
    // address on a taken branch or jump.
    output wire        o_retire_trap,
    // Asserted if the instruction is an `ebreak` instruction used to halt the
    // processor. This is used for debugging and testing purposes to end
    // a program.
    output wire        o_retire_halt,
    // The first register address read by the instruction being retired. If
    // the instruction does not read from a register (like `lui`), this
    // should be 5'd0.
    output wire [ 4:0] o_retire_rs1_raddr,
    // The second register address read by the instruction being retired. If
    // the instruction does not read from a second register (like `addi`), this
    // should be 5'd0.
    output wire [ 4:0] o_retire_rs2_raddr,
    // The first source register data read from the register file (in the
    // decode stage) for the instruction being retired. If rs1 is 5'd0, this
    // should also be 32'd0.
    output wire [31:0] o_retire_rs1_rdata,
    // The second source register data read from the register file (in the
    // decode stage) for the instruction being retired. If rs2 is 5'd0, this
    // should also be 32'd0.
    output wire [31:0] o_retire_rs2_rdata,
    // The destination register address written by the instruction being
    // retired. If the instruction does not write to a register (like `sw`),
    // this should be 5'd0.
    output wire [ 4:0] o_retire_rd_waddr,
    // The destination register data written to the register file in the
    // writeback stage by this instruction. If rd is 5'd0, this field is
    // ignored and can be treated as a don't care.
    output wire [31:0] o_retire_rd_wdata,
    // The current program counter of the instruction being retired - i.e.
    // the instruction memory address that the instruction was fetched from.
    output wire [31:0] o_retire_pc,
    // the next program counter after the instruction is retired. For most
    // instructions, this is `o_retire_pc + 4`, but must be the branch or jump
    // target for *taken* branches and jumps.
    output wire [31:0] o_retire_next_pc

`ifdef RISCV_FORMAL
    ,`RVFI_OUTPUTS,
`endif
);
    `default_nettype none

    // ========================================================================
    // Program Counter (PC) Register
    // ========================================================================
    reg [31:0] pc;
    wire [31:0] pc_next;

    always @(posedge i_clk) begin
        if (i_rst) begin
            pc <= RESET_ADDR;
        end else begin
            pc <= pc_next;
        end
    end

    // Connect PC to instruction memory
    assign o_imem_raddr = pc;
    wire [31:0] instruction = i_imem_rdata;

    // ========================================================================
    // Instruction Decode
    // ========================================================================
    // Extract instruction fields
    wire [6:0] opcode = instruction[6:0];
    wire [4:0] rd     = instruction[11:7];
    wire [2:0] funct3 = instruction[14:12];
    wire [4:0] rs1    = instruction[19:15];
    wire [4:0] rs2    = instruction[24:20];
    wire [6:0] funct7 = instruction[31:25];

    // Control signals from control unit
    wire [1:0] u_sel;
    wire [5:0] i_format;
    wire [2:0] bj_type;
    wire [5:0] alu_op;
    wire mem_read;
    wire mem_to_reg;
    wire mem_write;
    wire alu_src;
    wire reg_write;

    // Instantiate control unit
    ctl control_unit (
        .instruction(opcode),
        .U_sel(u_sel),
        .i_format(i_format),
        .bj_type(bj_type),
        .alu_op(alu_op),
        .mem_read(mem_read),
        .mem_to_reg(mem_to_reg),
        .mem_write(mem_write),
        .alu_src(alu_src),
        .reg_write(reg_write)
    );

    // ========================================================================
    // Immediate Generation
    // ========================================================================
    wire [31:0] immediate;

    imm imm_gen (
        .i_inst(instruction),
        .i_format(i_format),
        .o_immediate(immediate)
    );

    // ========================================================================
    // Register File
    // ========================================================================
    wire [31:0] rs1_data;
    wire [31:0] rs2_data;
    wire [31:0] rd_wdata;

    rf #(.BYPASS_EN(0)) register_file (
        .i_clk(i_clk),
        .i_rst(i_rst),
        .i_rs1_raddr(rs1),
        .o_rs1_rdata(rs1_data),
        .i_rs2_raddr(rs2),
        .o_rs2_rdata(rs2_data),
        .i_rd_wen(reg_write),
        .i_rd_waddr(rd),
        .i_rd_wdata(rd_wdata)
    );

    // ========================================================================
    // ALU Control
    // ========================================================================
    wire [2:0] alu_opsel;
    wire alu_sub;
    wire alu_unsigned;
    wire alu_arith;

    alu_ctl alu_control (
        .alu_op(alu_op),
        .instruction(instruction),
        .i_opsel(alu_opsel),
        .i_sub(alu_sub),
        .i_unsigned(alu_unsigned),
        .i_arith(alu_arith)
    );

    // ========================================================================
    // ALU
    // ========================================================================
    wire [31:0] alu_op1;
    wire [31:0] alu_op2;
    wire [31:0] alu_result;
    wire alu_eq;
    wire alu_slt;

    // ALU operand selection
    assign alu_op1 = rs1_data;
    assign alu_op2 = alu_src ? immediate : rs2_data;

    alu alu_unit (
        .i_opsel(alu_opsel),
        .i_sub(alu_sub),
        .i_unsigned(alu_unsigned),
        .i_arith(alu_arith),
        .i_op1(alu_op1),
        .i_op2(alu_op2),
        .o_result(alu_result),
        .o_eq(alu_eq),
        .o_slt(alu_slt)
    );

    // ========================================================================
    // Branch Logic
    // ========================================================================
    wire is_branch = (bj_type != 3'b000) && (opcode == 7'b1100011);
    wire is_jal    = (opcode == 7'b1101111);
    wire is_jalr   = (opcode == 7'b1100111);

    // Branch comparison logic
    reg branch_taken;
    always @(*) begin
        case (bj_type)
            3'b001: branch_taken = alu_eq;           // BEQ
            3'b010: branch_taken = ~alu_eq;          // BNE
            3'b011: branch_taken = alu_slt;          // BLT (signed)
            3'b100: branch_taken = ~alu_slt & ~alu_eq; // BGE (signed)
            3'b101: branch_taken = alu_slt;          // BLTU (unsigned)
            3'b110: branch_taken = ~alu_slt & ~alu_eq; // BGEU (unsigned)
            default: branch_taken = 1'b0;
        endcase
    end

    // ========================================================================
    // PC Update Logic
    // ========================================================================
    wire [31:0] pc_plus_4 = pc + 32'd4;
    wire [31:0] branch_target = pc + immediate;
    wire [31:0] jalr_target = (rs1_data + immediate) & ~32'd1;  // Clear LSB

    // PC selection logic
    assign pc_next = (is_branch && branch_taken) ? branch_target :
                     is_jal                       ? branch_target :
                     is_jalr                      ? jalr_target :
                                                    pc_plus_4;

    // ========================================================================
    // Data Memory Interface
    // ========================================================================
    // Memory address calculation (must be word-aligned)
    wire [31:0] mem_addr_unaligned = alu_result;
    wire [31:0] mem_addr_aligned = {mem_addr_unaligned[31:2], 2'b00};
    wire [1:0]  mem_byte_offset = mem_addr_unaligned[1:0];

    // Generate byte mask based on funct3 (load/store size) and byte offset
    reg [3:0] byte_mask;
    always @(*) begin
        case (funct3[1:0])  // funct3[1:0] determines size
            2'b00: begin  // Byte access (LB/LBU/SB)
                case (mem_byte_offset)
                    2'b00: byte_mask = 4'b0001;
                    2'b01: byte_mask = 4'b0010;
                    2'b10: byte_mask = 4'b0100;
                    2'b11: byte_mask = 4'b1000;
                endcase
            end
            2'b01: begin  // Halfword access (LH/LHU/SH)
                case (mem_byte_offset[1])
                    1'b0: byte_mask = 4'b0011;
                    1'b1: byte_mask = 4'b1100;
                endcase
            end
            2'b10: begin  // Word access (LW/SW)
                byte_mask = 4'b1111;
            end
            default: byte_mask = 4'b0000;
        endcase
    end

    // Store data alignment: shift rs2_data to correct byte lane
    reg [31:0] store_data_aligned;
    always @(*) begin
        case (funct3[1:0])
            2'b00: begin  // Byte store
                case (mem_byte_offset)
                    2'b00: store_data_aligned = {24'b0, rs2_data[7:0]};
                    2'b01: store_data_aligned = {16'b0, rs2_data[7:0], 8'b0};
                    2'b10: store_data_aligned = {8'b0, rs2_data[7:0], 16'b0};
                    2'b11: store_data_aligned = {rs2_data[7:0], 24'b0};
                endcase
            end
            2'b01: begin  // Halfword store
                case (mem_byte_offset[1])
                    1'b0: store_data_aligned = {16'b0, rs2_data[15:0]};
                    1'b1: store_data_aligned = {rs2_data[15:0], 16'b0};
                endcase
            end
            2'b10: begin  // Word store
                store_data_aligned = rs2_data;
            end
            default: store_data_aligned = 32'b0;
        endcase
    end

    // Load data alignment and sign extension
    reg [31:0] load_data_extended;
    wire mem_unsigned = funct3[2];  // funct3[2] = 1 for unsigned loads
    always @(*) begin
        case (funct3[1:0])
            2'b00: begin  // Byte load
                case (mem_byte_offset)
                    2'b00: load_data_extended = mem_unsigned ? {24'b0, i_dmem_rdata[7:0]} :
                                                               {{24{i_dmem_rdata[7]}}, i_dmem_rdata[7:0]};
                    2'b01: load_data_extended = mem_unsigned ? {24'b0, i_dmem_rdata[15:8]} :
                                                               {{24{i_dmem_rdata[15]}}, i_dmem_rdata[15:8]};
                    2'b10: load_data_extended = mem_unsigned ? {24'b0, i_dmem_rdata[23:16]} :
                                                               {{24{i_dmem_rdata[23]}}, i_dmem_rdata[23:16]};
                    2'b11: load_data_extended = mem_unsigned ? {24'b0, i_dmem_rdata[31:24]} :
                                                               {{24{i_dmem_rdata[31]}}, i_dmem_rdata[31:24]};
                endcase
            end
            2'b01: begin  // Halfword load
                case (mem_byte_offset[1])
                    1'b0: load_data_extended = mem_unsigned ? {16'b0, i_dmem_rdata[15:0]} :
                                                              {{16{i_dmem_rdata[15]}}, i_dmem_rdata[15:0]};
                    1'b1: load_data_extended = mem_unsigned ? {16'b0, i_dmem_rdata[31:16]} :
                                                              {{16{i_dmem_rdata[31]}}, i_dmem_rdata[31:16]};
                endcase
            end
            2'b10: begin  // Word load
                load_data_extended = i_dmem_rdata;
            end
            default: load_data_extended = 32'b0;
        endcase
    end

    // Data memory outputs
    assign o_dmem_addr = mem_addr_aligned;
    assign o_dmem_ren = mem_read;
    assign o_dmem_wen = mem_write;
    assign o_dmem_mask = byte_mask;
    assign o_dmem_wdata = store_data_aligned;

    // ========================================================================
    // Writeback Mux
    // ========================================================================
    // Determine writeback data source
    wire is_lui = (opcode == 7'b0110111);
    wire is_auipc = (opcode == 7'b0010111);
    wire write_pc_plus_4 = is_jal || is_jalr;

    assign rd_wdata = write_pc_plus_4 ? pc_plus_4 :
                      is_lui          ? immediate :
                      is_auipc        ? (pc + immediate) :
                      mem_to_reg      ? load_data_extended :
                                        alu_result;

    // ========================================================================
    // Retire Interface (for testbench)
    // ========================================================================
    assign o_retire_valid = 1'b1;  // Single-cycle: always retiring
    assign o_retire_inst = instruction;
    assign o_retire_trap = 1'b0;  // No traps in basic implementation
    assign o_retire_halt = 1'b0;  // No halt in basic implementation
    assign o_retire_rs1_raddr = rs1;
    assign o_retire_rs2_raddr = rs2;
    assign o_retire_rs1_rdata = rs1_data;
    assign o_retire_rs2_rdata = rs2_data;
    assign o_retire_rd_waddr = rd;
    assign o_retire_rd_wdata = rd_wdata;
    assign o_retire_pc = pc;
    assign o_retire_next_pc = pc_next;

endmodule

`default_nettype wire
