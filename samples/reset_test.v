module test(rst, cnt);

   input rst;
   output reg [15:0] cnt;

   always @(posedge clk) begin
      if (rst)
        cnt <= 16'd0;
      else if (cnt < 23)
        cnt <= cnt + 1;
      else
        cnt <= 16'd0;
   end

   always @* begin
      assert (cnt < 24);
   end
endmodule // test

