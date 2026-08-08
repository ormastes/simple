## K26 ML Carrier PMOD J2 serial pins (3.3V LVCMOS33).
##   pin 1 = TX -> H12   pin 2 = RX <- E10   pin 5 = GND
## Per doc/07_guide/hardware/fpga/kria_k26_ml_carrier_bringup.md.
set_property PACKAGE_PIN H12 [get_ports uart_tx]
set_property IOSTANDARD LVCMOS33 [get_ports uart_tx]
set_property PACKAGE_PIN E10 [get_ports uart_rx]
set_property IOSTANDARD LVCMOS33 [get_ports uart_rx]
## Real primary clock: STARTUPE3 CFGMCLK output pin (~50 MHz nominal on
## UltraScale+). Constraining the primitive PIN (not a net) makes Vivado
## propagate it; the 25 MHz core clock is auto-derived through BUFGCE_DIV/2.
## Reinstated 2026-07-24: the PS pl_clk0 path (zynq_ultra_ps_e IP) was found
## never to toggle under JTAG-only bring-up (ILA: HW_ILAS=0) -- see
## soc_top_rv64.vhd header. cfgmclk has no PS dependency (soc_top_rv32
## already boots + 981s-soaks on it).
create_clock -name cfgmclk -period 20.000 [get_pins u_startup/CFGMCLK]
## Async UART output -- no meaningful external timing relationship.
set_false_path -to [get_ports uart_tx]
