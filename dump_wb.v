module dump();
    initial begin
        $dumpfile ("wb_buttons_leds.vcd");
        $dumpvars (0, wb_buttons_leds);
        #1;
    end
endmodule
