PATH := ~/.solc-select/artifacts/:~/.solc-select/artifacts/solc-0.8.21:~/.solc-select/artifacts/solc-0.5.12:$(PATH)
certora-yusds       :; PATH=${PATH} certoraRun certora/YUsds.conf$(if $(rule), --rule $(rule),)$(if $(results), --wait_for_results all,)
certora-rate-setter :; PATH=${PATH} certoraRun certora/YUsdsRateSetter.conf$(if $(rule), --rule $(rule),)$(if $(results), --wait_for_results all,)
certora-mom         :; PATH=${PATH} certoraRun certora/YUsdsMom.conf$(if $(rule), --rule $(rule),)$(if $(results), --wait_for_results all,)
