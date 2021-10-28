#Run linting tests as a user
    # requires passwordless  ssh acces to epi3 and verilator installed locally
user_linting:
	cd ci/ && bash lint.sh
# CI version of linting script. Checks AXI and AHB versions of PMU with spyglass
docker_spyglass:
	cd ci/ && bash lint_CI.sh
	exit 0
