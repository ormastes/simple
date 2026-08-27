## K26 ML Carrier PMOD J2 serial pins (3.3V LVCMOS33).
##   pin 1 = TX -> H12   pin 2 = RX <- E10   pin 5 = GND
## Per doc/07_guide/hardware/fpga/kria_k26_ml_carrier_bringup.md.
set_property PACKAGE_PIN H12 [get_ports uart_tx]
set_property IOSTANDARD LVCMOS33 [get_ports uart_tx]
set_property PACKAGE_PIN E10 [get_ports uart_rx]
set_property IOSTANDARD LVCMOS33 [get_ports uart_rx]
## pl_clk0 (100 MHz) is auto-constrained by the zynq_ultra_ps_e IP;
## no manual create_clock here (the old cfgmclk clock is gone).
