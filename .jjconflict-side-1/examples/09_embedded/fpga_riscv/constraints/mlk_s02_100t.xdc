## MLK-S02-100T Constraint Scaffold
##
## Status:
## - board-specific placeholder scaffold only
## - no verified pin assignments yet
## - do not treat this file as a working hardware constraint set
##
## Intended board:
## - MiLianKe MLK-S02-100T
## - FPGA: XC7A100T-2FFG484I
## - Onboard clock: 25 MHz
## - User LEDs: 8
## - User buttons: 4
## - USB-UART bridge: CH340
##
## Required next step:
## - import or derive the vendor pin map / XDC
## - replace the commented templates below with authoritative pins
## - validate against a minimal LED/UART top-level before broader use

## Example template only:
## set_property PACKAGE_PIN <CLK25_PIN> [get_ports clk25]
## set_property IOSTANDARD LVCMOS33 [get_ports clk25]
## create_clock -period 40.000 -name sys_clk_25m [get_ports clk25]

## Example template only:
## set_property PACKAGE_PIN <RSTN_PIN> [get_ports rst_n]
## set_property IOSTANDARD LVCMOS33 [get_ports rst_n]

## Example template only:
## set_property PACKAGE_PIN <UART_TX_PIN> [get_ports uart_tx]
## set_property IOSTANDARD LVCMOS33 [get_ports uart_tx]
## set_property PACKAGE_PIN <UART_RX_PIN> [get_ports uart_rx]
## set_property IOSTANDARD LVCMOS33 [get_ports uart_rx]

## Example template only:
## set_property PACKAGE_PIN <LED0_PIN> [get_ports {led[0]}]
## set_property IOSTANDARD LVCMOS33 [get_ports {led[0]}]
## set_property PACKAGE_PIN <LED1_PIN> [get_ports {led[1]}]
## set_property IOSTANDARD LVCMOS33 [get_ports {led[1]}]
## set_property PACKAGE_PIN <LED2_PIN> [get_ports {led[2]}]
## set_property IOSTANDARD LVCMOS33 [get_ports {led[2]}]
## set_property PACKAGE_PIN <LED3_PIN> [get_ports {led[3]}]
## set_property IOSTANDARD LVCMOS33 [get_ports {led[3]}]
## set_property PACKAGE_PIN <LED4_PIN> [get_ports {led[4]}]
## set_property IOSTANDARD LVCMOS33 [get_ports {led[4]}]
## set_property PACKAGE_PIN <LED5_PIN> [get_ports {led[5]}]
## set_property IOSTANDARD LVCMOS33 [get_ports {led[5]}]
## set_property PACKAGE_PIN <LED6_PIN> [get_ports {led[6]}]
## set_property IOSTANDARD LVCMOS33 [get_ports {led[6]}]
## set_property PACKAGE_PIN <LED7_PIN> [get_ports {led[7]}]
## set_property IOSTANDARD LVCMOS33 [get_ports {led[7]}]

## Example template only:
## set_property PACKAGE_PIN <BTN0_PIN> [get_ports {btn[0]}]
## set_property IOSTANDARD LVCMOS33 [get_ports {btn[0]}]
## set_property PACKAGE_PIN <BTN1_PIN> [get_ports {btn[1]}]
## set_property IOSTANDARD LVCMOS33 [get_ports {btn[1]}]
## set_property PACKAGE_PIN <BTN2_PIN> [get_ports {btn[2]}]
## set_property IOSTANDARD LVCMOS33 [get_ports {btn[2]}]
## set_property PACKAGE_PIN <BTN3_PIN> [get_ports {btn[3]}]
## set_property IOSTANDARD LVCMOS33 [get_ports {btn[3]}]
