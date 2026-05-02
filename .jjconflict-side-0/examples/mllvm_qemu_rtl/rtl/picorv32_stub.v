module picorv32;
  reg [31:0] pc;
  reg halted;

  initial begin
    pc = 32'h8000_0000;
    halted = 1'b0;
  end
endmodule
