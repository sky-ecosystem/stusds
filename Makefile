PATH := ~/.solc-select/artifacts/:~/.solc-select/artifacts/solc-0.8.21:~/.solc-select/artifacts/solc-0.5.12:$(PATH)
certora-yusds :; PATH=${PATH} certoraRun certora/YUsds.conf$(if $(rule), --rule $(rule),)$(if $(results), --wait_for_results all,)
