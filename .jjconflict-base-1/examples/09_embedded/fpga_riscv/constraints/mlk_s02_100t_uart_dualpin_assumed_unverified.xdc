## MLK-S02-100T dual-UART-pin assumption probe.
## Non-authoritative: drives both previously assumed CH340 pins as UART TX to
## test whether the unverified RX/TX direction claim is swapped.

set_property PACKAGE_PIN W19 [get_ports clk25]
set_property IOSTANDARD LVCMOS33 [get_ports clk25]
create_clock -period 20.000 -name sys_clk_assumed_50m [get_ports clk25]

set_property PACKAGE_PIN L20 [get_ports uart_tx0]
set_property IOSTANDARD LVCMOS33 [get_ports uart_tx0]

set_property PACKAGE_PIN L19 [get_ports uart_tx1]
set_property IOSTANDARD LVCMOS33 [get_ports uart_tx1]

set_property PACKAGE_PIN M22 [get_ports {led[0]}]
set_property IOSTANDARD LVCMOS33 [get_ports {led[0]}]

