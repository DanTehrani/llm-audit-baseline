// SPDX-License-Identifier: BUSL-1.1
pragma solidity >=0.5.0 ^0.8.0 ^0.8.1 ^0.8.24;

// contracts/interfaces/core/IOracle.sol

/**
 * @title IOracle
 *
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 * @author Chef Kal-EL <chef.kal-el@bakerfi.xyz>
 *
 * @dev Interface for an Oracle providing price information with a precision.
 */
abstract contract IOracle {
    struct Price {
        uint256 price;
        uint256 lastUpdate;
    }

    struct PriceOptions {
        uint256 maxAge;
        uint256 maxConf;
    }

    error PriceOutdated();

    /**
     * @notice Retrieves the precision of the price information provided by the Oracle.
     * @dev This function is view-only and does not modify the state of the contract.
     * @return The precision of the Oracle's price information as a uint256.
     */
    function getPrecision() public view virtual returns (uint256);

    /**
     * @notice Retrieves the latest price information from the Oracle.
     * @dev This function is view-only and does not modify the state of the contract.
     * @return The latest price from the Oracle as a uint256.
     */
    function getLatestPrice() public view virtual returns (Price memory);

    /**
     * @notice Retrieves the latest price information from the Oracle and reverts whern the price
     * is outdated
     * @dev This function is view-only and does not modify the state of the contract.
     * @return The latest price from the Oracle as a uint256.
     */
    function getSafeLatestPrice(PriceOptions memory priceOptions) public view virtual returns (Price memory);
}

// contracts/libraries/MathLibrary.sol

/**
 * @title MathLibrary
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 * @dev Library for handling mathematical operations
 */
library MathLibrary {
    error InvalidDivDenominator();
    error OverflowDetected();

    uint256 private constant MAX_DIFFERENCE_DECIMALS = 64;

    /**
     * @notice Converts a value from one decimal precision to another.
     * @dev This function converts a `value` from a `from` decimal precision to a `to` decimal precision.
     *      It checks for overflow and reverts if the conversion would cause an overflow.
     * @param value The numerical value to convert.
     * @param from The current decimal precision of the `value`.
     * @param to The target decimal precision to convert to.
     * @return converted The value converted to the target decimal precision.
     * @custom:throws OverflowDetected if the difference between `from` and `to` is greater than or equal to `MAX_DIFFERENCE_DECIMALS`.
     * @custom:throws OverflowDetected if the multiplication required to increase precision would cause an overflow.
     */
    function toDecimals(uint256 value, uint8 from, uint8 to) internal pure returns (uint256 converted) {
        if (from > to) {
            if (from - to >= MAX_DIFFERENCE_DECIMALS) revert OverflowDetected();
            converted = value / (10 ** (from - to));
        } else if (to > from) {
            if (to - from >= MAX_DIFFERENCE_DECIMALS) revert OverflowDetected();
            uint256 factor = 10 ** (to - from);
            if (value > type(uint256).max / factor) revert OverflowDetected();
            converted = value * factor;
        } else {
            converted = value;
        }
    }

    /**
     * @dev Multiplies two unsigned integers `x` and `y`, then divides the result by `denominator`
     * and returns the result either rounded up or down based on the `roundUp` flag.
     *
     * @notice This function provides an option to round the division result up or down.
     * If `roundUp` is true, the function rounds up using the `mulDivUp` function;
     * otherwise, it rounds down using the `mulDivDown` function.
     * If `denominator` is zero, the function reverts with an `InvalidDivDenominator` error.
     *
     * @param x The first multiplicand as an unsigned integer.
     * @param y The second multiplicand as an unsigned integer.
     * @param denominator The divisor as an unsigned integer. Must not be zero.
     * @param roundUp A boolean flag indicating whether to round up or down.
     *
     * @return The result of the multiplication and division, rounded up or down based on `roundUp`.
     *
     * @custom:error InvalidDivDenominator Thrown if `denominator` is zero.
     */
    function mulDiv(uint256 x, uint256 y, uint256 denominator, bool roundUp) internal pure returns (uint256) {
        return roundUp ? mulDivUp(x, y, denominator) : mulDivDown(x, y, denominator);
    }
    /**
     * @dev Multiplies two unsigned integers `x` and `y`, then divides the result by `denominator`
     * and rounds the result up towards the next integer.
     *
     * @notice This function performs multiplication followed by division and rounds the result up towards
     * the next integer. If either `x` or `y` is zero, the function returns 0.
     * If `denominator` is zero, the function reverts with an `InvalidDivDenominator` error.
     *
     * @param x The first multiplicand as an unsigned integer.
     * @param y The second multiplicand as an unsigned integer.
     * @param denominator The divisor as an unsigned integer. Must not be zero.
     *
     * @return The result of the multiplication and division, rounded up towards the next integer.
     *
     * @custom:error InvalidDivDenominator Thrown if `denominator` is zero.
     */
    function mulDivUp(uint256 x, uint256 y, uint256 denominator) internal pure returns (uint256) {
        uint256 product = x * y;
        // Not Allowed Division by 0
        if (denominator == 0) revert InvalidDivDenominator();

        if (x == 0 || y == 0) {
            return 0;
        } else {
            // The traditional divUp formula is:
            // divUp(x, y) := (x + y - 1) / y
            // To avoid intermediate overflow in the addition, we distribute the division and get:
            // divUp(x, y) := (x - 1) / y + 1
            // Note that this requires x != 0, which we already tested for.
            return 1 + (product - 1) / denominator;
        }
    }

    /**
     * @dev Multiplies two unsigned integers `x` and `y`, then divides the result by `denominator` with truncation towards zero.
     * The function returns the result of the division.
     *
     * @notice This function performs multiplication followed by division. It truncates the result towards zero.
     * If either `x` or `y` is zero, the function returns 0.
     * If `denominator` is zero, the function reverts with an `InvalidDivDenominator` error.
     *
     * @param x The first multiplicand as an unsigned integer.
     * @param y The second multiplicand as an unsigned integer.
     * @param denominator The divisor as an unsigned integer. Must not be zero.
     *
     * @return The result of `(x * y) / denominator`, truncated towards zero.
     *
     * @custom:error InvalidDivDenominator Thrown if `denominator` is zero.
     */
    function mulDivDown(uint256 x, uint256 y, uint256 denominator) internal pure returns (uint256) {
        uint256 product = x * y;
        // Not Allowed: Division by 0
        if (denominator == 0) revert InvalidDivDenominator();

        if (x == 0 || y == 0) {
            return 0;
        } else {
            // Division down simply divides the product by the denominator
            // and truncates towards zero (which is the default behavior of division in Solidity).
            return product / denominator;
        }
    }
}

// node_modules/@morpho-org/morpho-blue/src/interfaces/IMorpho.sol

type Id is bytes32;

struct MarketParams {
    address loanToken;
    address collateralToken;
    address oracle;
    address irm;
    uint256 lltv;
}

/// @dev Warning: For `feeRecipient`, `supplyShares` does not contain the accrued shares since the last interest
/// accrual.
struct Position {
    uint256 supplyShares;
    uint128 borrowShares;
    uint128 collateral;
}

/// @dev Warning: `totalSupplyAssets` does not contain the accrued interest since the last interest accrual.
/// @dev Warning: `totalBorrowAssets` does not contain the accrued interest since the last interest accrual.
/// @dev Warning: `totalSupplyShares` does not contain the additional shares accrued by `feeRecipient` since the last
/// interest accrual.
struct Market {
    uint128 totalSupplyAssets;
    uint128 totalSupplyShares;
    uint128 totalBorrowAssets;
    uint128 totalBorrowShares;
    uint128 lastUpdate;
    uint128 fee;
}

struct Authorization {
    address authorizer;
    address authorized;
    bool isAuthorized;
    uint256 nonce;
    uint256 deadline;
}

struct Signature {
    uint8 v;
    bytes32 r;
    bytes32 s;
}

/// @dev This interface is used for factorizing IMorphoStaticTyping and IMorpho.
/// @dev Consider using the IMorpho interface instead of this one.
interface IMorphoBase {
    /// @notice The EIP-712 domain separator.
    /// @dev Warning: Every EIP-712 signed message based on this domain separator can be reused on another chain sharing
    /// the same chain id because the domain separator would be the same.
    function DOMAIN_SEPARATOR() external view returns (bytes32);

    /// @notice The owner of the contract.
    /// @dev It has the power to change the owner.
    /// @dev It has the power to set fees on markets and set the fee recipient.
    /// @dev It has the power to enable but not disable IRMs and LLTVs.
    function owner() external view returns (address);

    /// @notice The fee recipient of all markets.
    /// @dev The recipient receives the fees of a given market through a supply position on that market.
    function feeRecipient() external view returns (address);

    /// @notice Whether the `irm` is enabled.
    function isIrmEnabled(address irm) external view returns (bool);

    /// @notice Whether the `lltv` is enabled.
    function isLltvEnabled(uint256 lltv) external view returns (bool);

    /// @notice Whether `authorized` is authorized to modify `authorizer`'s position on all markets.
    /// @dev Anyone is authorized to modify their own positions, regardless of this variable.
    function isAuthorized(address authorizer, address authorized) external view returns (bool);

    /// @notice The `authorizer`'s current nonce. Used to prevent replay attacks with EIP-712 signatures.
    function nonce(address authorizer) external view returns (uint256);

    /// @notice Sets `newOwner` as `owner` of the contract.
    /// @dev Warning: No two-step transfer ownership.
    /// @dev Warning: The owner can be set to the zero address.
    function setOwner(address newOwner) external;

    /// @notice Enables `irm` as a possible IRM for market creation.
    /// @dev Warning: It is not possible to disable an IRM.
    function enableIrm(address irm) external;

    /// @notice Enables `lltv` as a possible LLTV for market creation.
    /// @dev Warning: It is not possible to disable a LLTV.
    function enableLltv(uint256 lltv) external;

    /// @notice Sets the `newFee` for the given market `marketParams`.
    /// @param newFee The new fee, scaled by WAD.
    /// @dev Warning: The recipient can be the zero address.
    function setFee(MarketParams memory marketParams, uint256 newFee) external;

    /// @notice Sets `newFeeRecipient` as `feeRecipient` of the fee.
    /// @dev Warning: If the fee recipient is set to the zero address, fees will accrue there and will be lost.
    /// @dev Modifying the fee recipient will allow the new recipient to claim any pending fees not yet accrued. To
    /// ensure that the current recipient receives all due fees, accrue interest manually prior to making any changes.
    function setFeeRecipient(address newFeeRecipient) external;

    /// @notice Creates the market `marketParams`.
    /// @dev Here is the list of assumptions on the market's dependencies (tokens, IRM and oracle) that guarantees
    /// Morpho behaves as expected:
    /// - The token should be ERC-20 compliant, except that it can omit return values on `transfer` and `transferFrom`.
    /// - The token balance of Morpho should only decrease on `transfer` and `transferFrom`. In particular, tokens with
    /// burn functions are not supported.
    /// - The token should not re-enter Morpho on `transfer` nor `transferFrom`.
    /// - The token balance of the sender (resp. receiver) should decrease (resp. increase) by exactly the given amount
    /// on `transfer` and `transferFrom`. In particular, tokens with fees on transfer are not supported.
    /// - The IRM should not re-enter Morpho.
    /// - The oracle should return a price with the correct scaling.
    /// @dev Here is a list of properties on the market's dependencies that could break Morpho's liveness properties
    /// (funds could get stuck):
    /// - The token can revert on `transfer` and `transferFrom` for a reason other than an approval or balance issue.
    /// - A very high amount of assets (~1e35) supplied or borrowed can make the computation of `toSharesUp` and
    /// `toSharesDown` overflow.
    /// - The IRM can revert on `borrowRate`.
    /// - A very high borrow rate returned by the IRM can make the computation of `interest` in `_accrueInterest`
    /// overflow.
    /// - The oracle can revert on `price`. Note that this can be used to prevent `borrow`, `withdrawCollateral` and
    /// `liquidate` from being used under certain market conditions.
    /// - A very high price returned by the oracle can make the computation of `maxBorrow` in `_isHealthy` overflow, or
    /// the computation of `assetsRepaid` in `liquidate` overflow.
    /// @dev The borrow share price of a market with less than 1e4 assets borrowed can be decreased by manipulations, to
    /// the point where `totalBorrowShares` is very large and borrowing overflows.
    function createMarket(MarketParams memory marketParams) external;

    /// @notice Supplies `assets` or `shares` on behalf of `onBehalf`, optionally calling back the caller's
    /// `onMorphoSupply` function with the given `data`.
    /// @dev Either `assets` or `shares` should be zero. Most use cases should rely on `assets` as an input so the
    /// caller is guaranteed to have `assets` tokens pulled from their balance, but the possibility to mint a specific
    /// amount of shares is given for full compatibility and precision.
    /// @dev Supplying a large amount can revert for overflow.
    /// @dev Supplying an amount of shares may lead to supply more or fewer assets than expected due to slippage.
    /// Consider using the `assets` parameter to avoid this.
    /// @param marketParams The market to supply assets to.
    /// @param assets The amount of assets to supply.
    /// @param shares The amount of shares to mint.
    /// @param onBehalf The address that will own the increased supply position.
    /// @param data Arbitrary data to pass to the `onMorphoSupply` callback. Pass empty data if not needed.
    /// @return assetsSupplied The amount of assets supplied.
    /// @return sharesSupplied The amount of shares minted.
    function supply(
        MarketParams memory marketParams,
        uint256 assets,
        uint256 shares,
        address onBehalf,
        bytes memory data
    ) external returns (uint256 assetsSupplied, uint256 sharesSupplied);

    /// @notice Withdraws `assets` or `shares` on behalf of `onBehalf` and sends the assets to `receiver`.
    /// @dev Either `assets` or `shares` should be zero. To withdraw max, pass the `shares`'s balance of `onBehalf`.
    /// @dev `msg.sender` must be authorized to manage `onBehalf`'s positions.
    /// @dev Withdrawing an amount corresponding to more shares than supplied will revert for underflow.
    /// @dev It is advised to use the `shares` input when withdrawing the full position to avoid reverts due to
    /// conversion roundings between shares and assets.
    /// @param marketParams The market to withdraw assets from.
    /// @param assets The amount of assets to withdraw.
    /// @param shares The amount of shares to burn.
    /// @param onBehalf The address of the owner of the supply position.
    /// @param receiver The address that will receive the withdrawn assets.
    /// @return assetsWithdrawn The amount of assets withdrawn.
    /// @return sharesWithdrawn The amount of shares burned.
    function withdraw(
        MarketParams memory marketParams,
        uint256 assets,
        uint256 shares,
        address onBehalf,
        address receiver
    ) external returns (uint256 assetsWithdrawn, uint256 sharesWithdrawn);

    /// @notice Borrows `assets` or `shares` on behalf of `onBehalf` and sends the assets to `receiver`.
    /// @dev Either `assets` or `shares` should be zero. Most use cases should rely on `assets` as an input so the
    /// caller is guaranteed to borrow `assets` of tokens, but the possibility to mint a specific amount of shares is
    /// given for full compatibility and precision.
    /// @dev `msg.sender` must be authorized to manage `onBehalf`'s positions.
    /// @dev Borrowing a large amount can revert for overflow.
    /// @dev Borrowing an amount of shares may lead to borrow fewer assets than expected due to slippage.
    /// Consider using the `assets` parameter to avoid this.
    /// @param marketParams The market to borrow assets from.
    /// @param assets The amount of assets to borrow.
    /// @param shares The amount of shares to mint.
    /// @param onBehalf The address that will own the increased borrow position.
    /// @param receiver The address that will receive the borrowed assets.
    /// @return assetsBorrowed The amount of assets borrowed.
    /// @return sharesBorrowed The amount of shares minted.
    function borrow(
        MarketParams memory marketParams,
        uint256 assets,
        uint256 shares,
        address onBehalf,
        address receiver
    ) external returns (uint256 assetsBorrowed, uint256 sharesBorrowed);

    /// @notice Repays `assets` or `shares` on behalf of `onBehalf`, optionally calling back the caller's
    /// `onMorphoReplay` function with the given `data`.
    /// @dev Either `assets` or `shares` should be zero. To repay max, pass the `shares`'s balance of `onBehalf`.
    /// @dev Repaying an amount corresponding to more shares than borrowed will revert for underflow.
    /// @dev It is advised to use the `shares` input when repaying the full position to avoid reverts due to conversion
    /// roundings between shares and assets.
    /// @dev An attacker can front-run a repay with a small repay making the transaction revert for underflow.
    /// @param marketParams The market to repay assets to.
    /// @param assets The amount of assets to repay.
    /// @param shares The amount of shares to burn.
    /// @param onBehalf The address of the owner of the debt position.
    /// @param data Arbitrary data to pass to the `onMorphoRepay` callback. Pass empty data if not needed.
    /// @return assetsRepaid The amount of assets repaid.
    /// @return sharesRepaid The amount of shares burned.
    function repay(
        MarketParams memory marketParams,
        uint256 assets,
        uint256 shares,
        address onBehalf,
        bytes memory data
    ) external returns (uint256 assetsRepaid, uint256 sharesRepaid);

    /// @notice Supplies `assets` of collateral on behalf of `onBehalf`, optionally calling back the caller's
    /// `onMorphoSupplyCollateral` function with the given `data`.
    /// @dev Interest are not accrued since it's not required and it saves gas.
    /// @dev Supplying a large amount can revert for overflow.
    /// @param marketParams The market to supply collateral to.
    /// @param assets The amount of collateral to supply.
    /// @param onBehalf The address that will own the increased collateral position.
    /// @param data Arbitrary data to pass to the `onMorphoSupplyCollateral` callback. Pass empty data if not needed.
    function supplyCollateral(MarketParams memory marketParams, uint256 assets, address onBehalf, bytes memory data)
        external;

    /// @notice Withdraws `assets` of collateral on behalf of `onBehalf` and sends the assets to `receiver`.
    /// @dev `msg.sender` must be authorized to manage `onBehalf`'s positions.
    /// @dev Withdrawing an amount corresponding to more collateral than supplied will revert for underflow.
    /// @param marketParams The market to withdraw collateral from.
    /// @param assets The amount of collateral to withdraw.
    /// @param onBehalf The address of the owner of the collateral position.
    /// @param receiver The address that will receive the collateral assets.
    function withdrawCollateral(MarketParams memory marketParams, uint256 assets, address onBehalf, address receiver)
        external;

    /// @notice Liquidates the given `repaidShares` of debt asset or seize the given `seizedAssets` of collateral on the
    /// given market `marketParams` of the given `borrower`'s position, optionally calling back the caller's
    /// `onMorphoLiquidate` function with the given `data`.
    /// @dev Either `seizedAssets` or `repaidShares` should be zero.
    /// @dev Seizing more than the collateral balance will underflow and revert without any error message.
    /// @dev Repaying more than the borrow balance will underflow and revert without any error message.
    /// @dev An attacker can front-run a liquidation with a small repay making the transaction revert for underflow.
    /// @param marketParams The market of the position.
    /// @param borrower The owner of the position.
    /// @param seizedAssets The amount of collateral to seize.
    /// @param repaidShares The amount of shares to repay.
    /// @param data Arbitrary data to pass to the `onMorphoLiquidate` callback. Pass empty data if not needed.
    /// @return The amount of assets seized.
    /// @return The amount of assets repaid.
    function liquidate(
        MarketParams memory marketParams,
        address borrower,
        uint256 seizedAssets,
        uint256 repaidShares,
        bytes memory data
    ) external returns (uint256, uint256);

    /// @notice Executes a flash loan.
    /// @dev Flash loans have access to the whole balance of the contract (the liquidity and deposited collateral of all
    /// markets combined, plus donations).
    /// @dev Warning: Not ERC-3156 compliant but compatibility is easily reached:
    /// - `flashFee` is zero.
    /// - `maxFlashLoan` is the token's balance of this contract.
    /// - The receiver of `assets` is the caller.
    /// @param token The token to flash loan.
    /// @param assets The amount of assets to flash loan.
    /// @param data Arbitrary data to pass to the `onMorphoFlashLoan` callback.
    function flashLoan(address token, uint256 assets, bytes calldata data) external;

    /// @notice Sets the authorization for `authorized` to manage `msg.sender`'s positions.
    /// @param authorized The authorized address.
    /// @param newIsAuthorized The new authorization status.
    function setAuthorization(address authorized, bool newIsAuthorized) external;

    /// @notice Sets the authorization for `authorization.authorized` to manage `authorization.authorizer`'s positions.
    /// @dev Warning: Reverts if the signature has already been submitted.
    /// @dev The signature is malleable, but it has no impact on the security here.
    /// @dev The nonce is passed as argument to be able to revert with a different error message.
    /// @param authorization The `Authorization` struct.
    /// @param signature The signature.
    function setAuthorizationWithSig(Authorization calldata authorization, Signature calldata signature) external;

    /// @notice Accrues interest for the given market `marketParams`.
    function accrueInterest(MarketParams memory marketParams) external;

    /// @notice Returns the data stored on the different `slots`.
    function extSloads(bytes32[] memory slots) external view returns (bytes32[] memory);
}

/// @dev This interface is inherited by Morpho so that function signatures are checked by the compiler.
/// @dev Consider using the IMorpho interface instead of this one.
interface IMorphoStaticTyping is IMorphoBase {
    /// @notice The state of the position of `user` on the market corresponding to `id`.
    /// @dev Warning: For `feeRecipient`, `supplyShares` does not contain the accrued shares since the last interest
    /// accrual.
    function position(Id id, address user)
        external
        view
        returns (uint256 supplyShares, uint128 borrowShares, uint128 collateral);

    /// @notice The state of the market corresponding to `id`.
    /// @dev Warning: `totalSupplyAssets` does not contain the accrued interest since the last interest accrual.
    /// @dev Warning: `totalBorrowAssets` does not contain the accrued interest since the last interest accrual.
    /// @dev Warning: `totalSupplyShares` does not contain the accrued shares by `feeRecipient` since the last interest
    /// accrual.
    function market(Id id)
        external
        view
        returns (
            uint128 totalSupplyAssets,
            uint128 totalSupplyShares,
            uint128 totalBorrowAssets,
            uint128 totalBorrowShares,
            uint128 lastUpdate,
            uint128 fee
        );

    /// @notice The market params corresponding to `id`.
    /// @dev This mapping is not used in Morpho. It is there to enable reducing the cost associated to calldata on layer
    /// 2s by creating a wrapper contract with functions that take `id` as input instead of `marketParams`.
    function idToMarketParams(Id id)
        external
        view
        returns (address loanToken, address collateralToken, address oracle, address irm, uint256 lltv);
}

/// @title IMorpho
/// @author Morpho Labs
/// @custom:contact security@morpho.org
/// @dev Use this interface for Morpho to have access to all the functions with the appropriate function signatures.
interface IMorpho is IMorphoBase {
    /// @notice The state of the position of `user` on the market corresponding to `id`.
    /// @dev Warning: For `feeRecipient`, `p.supplyShares` does not contain the accrued shares since the last interest
    /// accrual.
    function position(Id id, address user) external view returns (Position memory p);

    /// @notice The state of the market corresponding to `id`.
    /// @dev Warning: `m.totalSupplyAssets` does not contain the accrued interest since the last interest accrual.
    /// @dev Warning: `m.totalBorrowAssets` does not contain the accrued interest since the last interest accrual.
    /// @dev Warning: `m.totalSupplyShares` does not contain the accrued shares by `feeRecipient` since the last
    /// interest accrual.
    function market(Id id) external view returns (Market memory m);

    /// @notice The market params corresponding to `id`.
    /// @dev This mapping is not used in Morpho. It is there to enable reducing the cost associated to calldata on layer
    /// 2s by creating a wrapper contract with functions that take `id` as input instead of `marketParams`.
    function idToMarketParams(Id id) external view returns (MarketParams memory);
}

// node_modules/@morpho-org/morpho-blue/src/libraries/ErrorsLib.sol

/// @title ErrorsLib
/// @author Morpho Labs
/// @custom:contact security@morpho.org
/// @notice Library exposing error messages.
library ErrorsLib {
    /// @notice Thrown when the caller is not the owner.
    string internal constant NOT_OWNER = "not owner";

    /// @notice Thrown when the LLTV to enable exceeds the maximum LLTV.
    string internal constant MAX_LLTV_EXCEEDED = "max LLTV exceeded";

    /// @notice Thrown when the fee to set exceeds the maximum fee.
    string internal constant MAX_FEE_EXCEEDED = "max fee exceeded";

    /// @notice Thrown when the value is already set.
    string internal constant ALREADY_SET = "already set";

    /// @notice Thrown when the IRM is not enabled at market creation.
    string internal constant IRM_NOT_ENABLED = "IRM not enabled";

    /// @notice Thrown when the LLTV is not enabled at market creation.
    string internal constant LLTV_NOT_ENABLED = "LLTV not enabled";

    /// @notice Thrown when the market is already created.
    string internal constant MARKET_ALREADY_CREATED = "market already created";

    /// @notice Thrown when a token to transfer doesn't have code.
    string internal constant NO_CODE = "no code";

    /// @notice Thrown when the market is not created.
    string internal constant MARKET_NOT_CREATED = "market not created";

    /// @notice Thrown when not exactly one of the input amount is zero.
    string internal constant INCONSISTENT_INPUT = "inconsistent input";

    /// @notice Thrown when zero assets is passed as input.
    string internal constant ZERO_ASSETS = "zero assets";

    /// @notice Thrown when a zero address is passed as input.
    string internal constant ZERO_ADDRESS = "zero address";

    /// @notice Thrown when the caller is not authorized to conduct an action.
    string internal constant UNAUTHORIZED = "unauthorized";

    /// @notice Thrown when the collateral is insufficient to `borrow` or `withdrawCollateral`.
    string internal constant INSUFFICIENT_COLLATERAL = "insufficient collateral";

    /// @notice Thrown when the liquidity is insufficient to `withdraw` or `borrow`.
    string internal constant INSUFFICIENT_LIQUIDITY = "insufficient liquidity";

    /// @notice Thrown when the position to liquidate is healthy.
    string internal constant HEALTHY_POSITION = "position is healthy";

    /// @notice Thrown when the authorization signature is invalid.
    string internal constant INVALID_SIGNATURE = "invalid signature";

    /// @notice Thrown when the authorization signature is expired.
    string internal constant SIGNATURE_EXPIRED = "signature expired";

    /// @notice Thrown when the nonce is invalid.
    string internal constant INVALID_NONCE = "invalid nonce";

    /// @notice Thrown when a token transfer reverted.
    string internal constant TRANSFER_REVERTED = "transfer reverted";

    /// @notice Thrown when a token transfer returned false.
    string internal constant TRANSFER_RETURNED_FALSE = "transfer returned false";

    /// @notice Thrown when a token transferFrom reverted.
    string internal constant TRANSFER_FROM_REVERTED = "transferFrom reverted";

    /// @notice Thrown when a token transferFrom returned false
    string internal constant TRANSFER_FROM_RETURNED_FALSE = "transferFrom returned false";

    /// @notice Thrown when the maximum uint128 is exceeded.
    string internal constant MAX_UINT128_EXCEEDED = "max uint128 exceeded";
}

// node_modules/@morpho-org/morpho-blue/src/libraries/MathLib.sol

uint256 constant WAD = 1e18;

/// @title MathLib
/// @author Morpho Labs
/// @custom:contact security@morpho.org
/// @notice Library to manage fixed-point arithmetic.
library MathLib {
    /// @dev Returns (`x` * `y`) / `WAD` rounded down.
    function wMulDown(uint256 x, uint256 y) internal pure returns (uint256) {
        return mulDivDown(x, y, WAD);
    }

    /// @dev Returns (`x` * `WAD`) / `y` rounded down.
    function wDivDown(uint256 x, uint256 y) internal pure returns (uint256) {
        return mulDivDown(x, WAD, y);
    }

    /// @dev Returns (`x` * `WAD`) / `y` rounded up.
    function wDivUp(uint256 x, uint256 y) internal pure returns (uint256) {
        return mulDivUp(x, WAD, y);
    }

    /// @dev Returns (`x` * `y`) / `d` rounded down.
    function mulDivDown(uint256 x, uint256 y, uint256 d) internal pure returns (uint256) {
        return (x * y) / d;
    }

    /// @dev Returns (`x` * `y`) / `d` rounded up.
    function mulDivUp(uint256 x, uint256 y, uint256 d) internal pure returns (uint256) {
        return (x * y + (d - 1)) / d;
    }

    /// @dev Returns the sum of the first three non-zero terms of a Taylor expansion of e^(nx) - 1, to approximate a
    /// continuous compound interest rate.
    function wTaylorCompounded(uint256 x, uint256 n) internal pure returns (uint256) {
        uint256 firstTerm = x * n;
        uint256 secondTerm = mulDivDown(firstTerm, firstTerm, 2 * WAD);
        uint256 thirdTerm = mulDivDown(secondTerm, firstTerm, 3 * WAD);

        return firstTerm + secondTerm + thirdTerm;
    }
}

// node_modules/@openzeppelin/contracts/security/ReentrancyGuard.sol

// OpenZeppelin Contracts (last updated v4.9.0) (security/ReentrancyGuard.sol)

/**
 * @dev Contract module that helps prevent reentrant calls to a function.
 *
 * Inheriting from `ReentrancyGuard` will make the {nonReentrant} modifier
 * available, which can be applied to functions to make sure there are no nested
 * (reentrant) calls to them.
 *
 * Note that because there is a single `nonReentrant` guard, functions marked as
 * `nonReentrant` may not call one another. This can be worked around by making
 * those functions `private`, and then adding `external` `nonReentrant` entry
 * points to them.
 *
 * TIP: If you would like to learn more about reentrancy and alternative ways
 * to protect against it, check out our blog post
 * https://blog.openzeppelin.com/reentrancy-after-istanbul/[Reentrancy After Istanbul].
 */
abstract contract ReentrancyGuard {
    // Booleans are more expensive than uint256 or any type that takes up a full
    // word because each write operation emits an extra SLOAD to first read the
    // slot's contents, replace the bits taken up by the boolean, and then write
    // back. This is the compiler's defense against contract upgrades and
    // pointer aliasing, and it cannot be disabled.

    // The values being non-zero value makes deployment a bit more expensive,
    // but in exchange the refund on every call to nonReentrant will be lower in
    // amount. Since refunds are capped to a percentage of the total
    // transaction's gas, it is best to keep them low in cases like this one, to
    // increase the likelihood of the full refund coming into effect.
    uint256 private constant _NOT_ENTERED = 1;
    uint256 private constant _ENTERED = 2;

    uint256 private _status;

    constructor() {
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Prevents a contract from calling itself, directly or indirectly.
     * Calling a `nonReentrant` function from another `nonReentrant`
     * function is not supported. It is possible to prevent this from happening
     * by making the `nonReentrant` function external, and making it call a
     * `private` function that does the actual work.
     */
    modifier nonReentrant() {
        _nonReentrantBefore();
        _;
        _nonReentrantAfter();
    }

    function _nonReentrantBefore() private {
        // On the first call to nonReentrant, _status will be _NOT_ENTERED
        require(_status != _ENTERED, "ReentrancyGuard: reentrant call");

        // Any calls to nonReentrant after this point will fail
        _status = _ENTERED;
    }

    function _nonReentrantAfter() private {
        // By storing the original value once again, a refund is triggered (see
        // https://eips.ethereum.org/EIPS/eip-2200)
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Returns true if the reentrancy guard is currently set to "entered", which indicates there is a
     * `nonReentrant` function in the call stack.
     */
    function _reentrancyGuardEntered() internal view returns (bool) {
        return _status == _ENTERED;
    }
}

// node_modules/@openzeppelin/contracts/token/ERC20/IERC20.sol

// OpenZeppelin Contracts (last updated v4.9.0) (token/ERC20/IERC20.sol)

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);

    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `from` to `to` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address from, address to, uint256 amount) external returns (bool);
}

// node_modules/@openzeppelin/contracts/token/ERC20/extensions/IERC20Permit.sol

// OpenZeppelin Contracts (last updated v4.9.4) (token/ERC20/extensions/IERC20Permit.sol)

/**
 * @dev Interface of the ERC20 Permit extension allowing approvals to be made via signatures, as defined in
 * https://eips.ethereum.org/EIPS/eip-2612[EIP-2612].
 *
 * Adds the {permit} method, which can be used to change an account's ERC20 allowance (see {IERC20-allowance}) by
 * presenting a message signed by the account. By not relying on {IERC20-approve}, the token holder account doesn't
 * need to send a transaction, and thus is not required to hold Ether at all.
 *
 * ==== Security Considerations
 *
 * There are two important considerations concerning the use of `permit`. The first is that a valid permit signature
 * expresses an allowance, and it should not be assumed to convey additional meaning. In particular, it should not be
 * considered as an intention to spend the allowance in any specific way. The second is that because permits have
 * built-in replay protection and can be submitted by anyone, they can be frontrun. A protocol that uses permits should
 * take this into consideration and allow a `permit` call to fail. Combining these two aspects, a pattern that may be
 * generally recommended is:
 *
 * ```solidity
 * function doThingWithPermit(..., uint256 value, uint256 deadline, uint8 v, bytes32 r, bytes32 s) public {
 *     try token.permit(msg.sender, address(this), value, deadline, v, r, s) {} catch {}
 *     doThing(..., value);
 * }
 *
 * function doThing(..., uint256 value) public {
 *     token.safeTransferFrom(msg.sender, address(this), value);
 *     ...
 * }
 * ```
 *
 * Observe that: 1) `msg.sender` is used as the owner, leaving no ambiguity as to the signer intent, and 2) the use of
 * `try/catch` allows the permit to fail and makes the code tolerant to frontrunning. (See also
 * {SafeERC20-safeTransferFrom}).
 *
 * Additionally, note that smart contract wallets (such as Argent or Safe) are not able to produce permit signatures, so
 * contracts should have entry points that don't rely on permit.
 */
interface IERC20Permit {
    /**
     * @dev Sets `value` as the allowance of `spender` over ``owner``'s tokens,
     * given ``owner``'s signed approval.
     *
     * IMPORTANT: The same issues {IERC20-approve} has related to transaction
     * ordering also apply here.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `deadline` must be a timestamp in the future.
     * - `v`, `r` and `s` must be a valid `secp256k1` signature from `owner`
     * over the EIP712-formatted function arguments.
     * - the signature must use ``owner``'s current nonce (see {nonces}).
     *
     * For more information on the signature format, see the
     * https://eips.ethereum.org/EIPS/eip-2612#specification[relevant EIP
     * section].
     *
     * CAUTION: See Security Considerations above.
     */
    function permit(
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external;

    /**
     * @dev Returns the current nonce for `owner`. This value must be
     * included whenever a signature is generated for {permit}.
     *
     * Every successful call to {permit} increases ``owner``'s nonce by one. This
     * prevents a signature from being used multiple times.
     */
    function nonces(address owner) external view returns (uint256);

    /**
     * @dev Returns the domain separator used in the encoding of the signature for {permit}, as defined by {EIP712}.
     */
    // solhint-disable-next-line func-name-mixedcase
    function DOMAIN_SEPARATOR() external view returns (bytes32);
}

// node_modules/@openzeppelin/contracts/utils/Address.sol

// OpenZeppelin Contracts (last updated v4.9.0) (utils/Address.sol)

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     *
     * Furthermore, `isContract` will also return true if the target contract within
     * the same transaction is already scheduled for destruction by `SELFDESTRUCT`,
     * which only has an effect at the end of a transaction.
     * ====
     *
     * [IMPORTANT]
     * ====
     * You shouldn't rely on `isContract` to protect against flash loan attacks!
     *
     * Preventing calls from contracts is highly discouraged. It breaks composability, breaks support for smart wallets
     * like Gnosis Safe, and does not provide security since it can be circumvented by calling from a contract
     * constructor.
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize/address.code.length, which returns 0
        // for contracts in construction, since the code is only stored at the end
        // of the constructor execution.

        return account.code.length > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://consensys.net/diligence/blog/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.8.0/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        (bool success, ) = recipient.call{value: amount}("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain `call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        (bool success, bytes memory returndata) = target.call{value: value}(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        (bool success, bytes memory returndata) = target.staticcall(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Tool to verify that a low level call to smart-contract was successful, and revert (either by bubbling
     * the revert reason or using the provided one) in case of unsuccessful call or if target was not a contract.
     *
     * _Available since v4.8._
     */
    function verifyCallResultFromTarget(
        address target,
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        if (success) {
            if (returndata.length == 0) {
                // only check isContract if the call was successful and the return data is empty
                // otherwise we already know that it was a contract
                require(isContract(target), "Address: call to non-contract");
            }
            return returndata;
        } else {
            _revert(returndata, errorMessage);
        }
    }

    /**
     * @dev Tool to verify that a low level call was successful, and revert if it wasn't, either by bubbling the
     * revert reason or using the provided one.
     *
     * _Available since v4.3._
     */
    function verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            _revert(returndata, errorMessage);
        }
    }

    function _revert(bytes memory returndata, string memory errorMessage) private pure {
        // Look for revert reason and bubble it up if present
        if (returndata.length > 0) {
            // The easiest way to bubble the revert reason is using memory via assembly
            /// @solidity memory-safe-assembly
            assembly {
                let returndata_size := mload(returndata)
                revert(add(32, returndata), returndata_size)
            }
        } else {
            revert(errorMessage);
        }
    }
}

// node_modules/@openzeppelin/contracts/utils/Context.sol

// OpenZeppelin Contracts (last updated v4.9.4) (utils/Context.sol)

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }

    function _contextSuffixLength() internal view virtual returns (uint256) {
        return 0;
    }
}

// contracts/interfaces/core/IStrategy.sol

/**
 * @title Strategy Inteface to deploy and ERC-20 on an investment strategy
 *
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 * @author Chef Kal-EL <chef.kal-el@bakerfi.xyz>
 *
 * @notice Deploys an Any Standard ERC-20 and harvests yield
 */
interface IStrategy {
    /**
     * @dev Emitted when a strategy is deployed.
     *
     * This event provides information about the address deploying the strategy and the deployed amount.
     *
     * @param from The address deploying the strategy.
     * @param amount The amount deployed in the strategy.
     */
    event StrategyDeploy(address indexed from, uint256 indexed amount);

    /**
     * @dev Emitted when a strategy is undeployed.
     *
     * This event provides information about the address undeploying the strategy and the undeployed amount.
     *
     * @param from The address undeploying the strategy.
     * @param amount The amount undeployed from the strategy.
     */
    event StrategyUndeploy(address indexed from, uint256 indexed amount);

    /**
     * @dev Emitted when a strategy generates a profit.
     *
     * This event provides information about the profit amount generated by the strategy.
     *
     * @param amount The profit amount generated by the strategy.
     */
    event StrategyProfit(uint256 indexed amount);

    /**
     * @dev Emitted when a strategy incurs a loss.
     *
     * This event provides information about the loss amount incurred by the strategy.
     *
     * @param amount The loss amount incurred by the strategy.
     */
    event StrategyLoss(uint256 indexed amount);

    /**
     * @dev Emitted when a strategy's deployed amount is updated.
     *
     * This event provides information about the new deployment amount of the strategy.
     *
     * @param newDeployment The new deployment amount of the strategy.
     */
    event StrategyAmountUpdate(uint256 indexed newDeployment);

    /**
     * @dev Deploys funds in the AAVEv3 strategy
     *
     * @return deployedAmount The amount deployed in the AAVEv3 strategy after leveraging.
     *
     */
    function deploy(uint256 amount) external returns (uint256 deployedAmount);

    /**
     * @notice Harvests the strategy by yield and rebalances the strategy
     *
     * @return balanceChange The change in strategy balance as an int256 value.
     */
    function harvest() external returns (int256 balanceChange);

    /**
     * @dev Initiates the undeployment process by adjusting the contract's position and performing a flash loan.
     *
     * @param amount The amount of ETH to undeploy.
     * @return undeployedAmount The actual undeployed amount of ETH.
     */
    function undeploy(uint256 amount) external returns (uint256 undeployedAmount);

    /**
     * @dev Retrieves the total owned assets by the Strategy in
     *
     * @return assets The total owned assets in the strategy.
     */
    function totalAssets() external view returns (uint256 assets);

    /**
     * The Asset deployed on this strategy
     */
    function asset() external view returns (address);
}

// node_modules/@morpho-org/morpho-blue/src/interfaces/IIrm.sol

/// @title IIrm
/// @author Morpho Labs
/// @custom:contact security@morpho.org
/// @notice Interface that Interest Rate Models (IRMs) used by Morpho must implement.
interface IIrm {
    /// @notice Returns the borrow rate per second (scaled by WAD) of the market `marketParams`.
    /// @dev Assumes that `market` corresponds to `marketParams`.
    function borrowRate(MarketParams memory marketParams, Market memory market) external returns (uint256);

    /// @notice Returns the borrow rate per second (scaled by WAD) of the market `marketParams` without modifying any
    /// storage.
    /// @dev Assumes that `market` corresponds to `marketParams`.
    function borrowRateView(MarketParams memory marketParams, Market memory market) external view returns (uint256);
}

// node_modules/@morpho-org/morpho-blue/src/libraries/MarketParamsLib.sol

/// @title MarketParamsLib
/// @author Morpho Labs
/// @custom:contact security@morpho.org
/// @notice Library to convert a market to its id.
library MarketParamsLib {
    /// @notice The length of the data used to compute the id of a market.
    /// @dev The length is 5 * 32 because `MarketParams` has 5 variables of 32 bytes each.
    uint256 internal constant MARKET_PARAMS_BYTES_LENGTH = 5 * 32;

    /// @notice Returns the id of the market `marketParams`.
    function id(MarketParams memory marketParams) internal pure returns (Id marketParamsId) {
        assembly ("memory-safe") {
            marketParamsId := keccak256(marketParams, MARKET_PARAMS_BYTES_LENGTH)
        }
    }
}

// node_modules/@morpho-org/morpho-blue/src/libraries/SharesMathLib.sol

/// @title SharesMathLib
/// @author Morpho Labs
/// @custom:contact security@morpho.org
/// @notice Shares management library.
/// @dev This implementation mitigates share price manipulations, using OpenZeppelin's method of virtual shares:
/// https://docs.openzeppelin.com/contracts/4.x/erc4626#inflation-attack.
library SharesMathLib {
    using MathLib for uint256;

    /// @dev The number of virtual shares has been chosen low enough to prevent overflows, and high enough to ensure
    /// high precision computations.
    /// @dev Virtual shares can never be redeemed for the assets they are entitled to, but it is assumed the share price
    /// stays low enough not to inflate these assets to a significant value.
    /// @dev Warning: The assets to which virtual borrow shares are entitled behave like unrealizable bad debt.
    uint256 internal constant VIRTUAL_SHARES = 1e6;

    /// @dev A number of virtual assets of 1 enforces a conversion rate between shares and assets when a market is
    /// empty.
    uint256 internal constant VIRTUAL_ASSETS = 1;

    /// @dev Calculates the value of `assets` quoted in shares, rounding down.
    function toSharesDown(uint256 assets, uint256 totalAssets, uint256 totalShares) internal pure returns (uint256) {
        return assets.mulDivDown(totalShares + VIRTUAL_SHARES, totalAssets + VIRTUAL_ASSETS);
    }

    /// @dev Calculates the value of `shares` quoted in assets, rounding down.
    function toAssetsDown(uint256 shares, uint256 totalAssets, uint256 totalShares) internal pure returns (uint256) {
        return shares.mulDivDown(totalAssets + VIRTUAL_ASSETS, totalShares + VIRTUAL_SHARES);
    }

    /// @dev Calculates the value of `assets` quoted in shares, rounding up.
    function toSharesUp(uint256 assets, uint256 totalAssets, uint256 totalShares) internal pure returns (uint256) {
        return assets.mulDivUp(totalShares + VIRTUAL_SHARES, totalAssets + VIRTUAL_ASSETS);
    }

    /// @dev Calculates the value of `shares` quoted in assets, rounding up.
    function toAssetsUp(uint256 shares, uint256 totalAssets, uint256 totalShares) internal pure returns (uint256) {
        return shares.mulDivUp(totalAssets + VIRTUAL_ASSETS, totalShares + VIRTUAL_SHARES);
    }
}

// node_modules/@morpho-org/morpho-blue/src/libraries/UtilsLib.sol

/// @title UtilsLib
/// @author Morpho Labs
/// @custom:contact security@morpho.org
/// @notice Library exposing helpers.
/// @dev Inspired by https://github.com/morpho-org/morpho-utils.
library UtilsLib {
    /// @dev Returns true if there is exactly one zero among `x` and `y`.
    function exactlyOneZero(uint256 x, uint256 y) internal pure returns (bool z) {
        assembly {
            z := xor(iszero(x), iszero(y))
        }
    }

    /// @dev Returns the min of `x` and `y`.
    function min(uint256 x, uint256 y) internal pure returns (uint256 z) {
        assembly {
            z := xor(x, mul(xor(x, y), lt(y, x)))
        }
    }

    /// @dev Returns `x` safely cast to uint128.
    function toUint128(uint256 x) internal pure returns (uint128) {
        require(x <= type(uint128).max, ErrorsLib.MAX_UINT128_EXCEEDED);
        return uint128(x);
    }

    /// @dev Returns max(0, x - y).
    function zeroFloorSub(uint256 x, uint256 y) internal pure returns (uint256 z) {
        assembly {
            z := mul(gt(x, y), sub(x, y))
        }
    }
}

// node_modules/@morpho-org/morpho-blue/src/libraries/periphery/MorphoStorageLib.sol

/// @title MorphoStorageLib
/// @author Morpho Labs
/// @custom:contact security@morpho.org
/// @notice Helper library exposing getters to access Morpho storage variables' slot.
/// @dev This library is not used in Morpho itself and is intended to be used by integrators.
library MorphoStorageLib {
    /* SLOTS */

    uint256 internal constant OWNER_SLOT = 0;
    uint256 internal constant FEE_RECIPIENT_SLOT = 1;
    uint256 internal constant POSITION_SLOT = 2;
    uint256 internal constant MARKET_SLOT = 3;
    uint256 internal constant IS_IRM_ENABLED_SLOT = 4;
    uint256 internal constant IS_LLTV_ENABLED_SLOT = 5;
    uint256 internal constant IS_AUTHORIZED_SLOT = 6;
    uint256 internal constant NONCE_SLOT = 7;
    uint256 internal constant ID_TO_MARKET_PARAMS_SLOT = 8;

    /* SLOT OFFSETS */

    uint256 internal constant LOAN_TOKEN_OFFSET = 0;
    uint256 internal constant COLLATERAL_TOKEN_OFFSET = 1;
    uint256 internal constant ORACLE_OFFSET = 2;
    uint256 internal constant IRM_OFFSET = 3;
    uint256 internal constant LLTV_OFFSET = 4;

    uint256 internal constant SUPPLY_SHARES_OFFSET = 0;
    uint256 internal constant BORROW_SHARES_AND_COLLATERAL_OFFSET = 1;

    uint256 internal constant TOTAL_SUPPLY_ASSETS_AND_SHARES_OFFSET = 0;
    uint256 internal constant TOTAL_BORROW_ASSETS_AND_SHARES_OFFSET = 1;
    uint256 internal constant LAST_UPDATE_AND_FEE_OFFSET = 2;

    /* GETTERS */

    function ownerSlot() internal pure returns (bytes32) {
        return bytes32(OWNER_SLOT);
    }

    function feeRecipientSlot() internal pure returns (bytes32) {
        return bytes32(FEE_RECIPIENT_SLOT);
    }

    function positionSupplySharesSlot(Id id, address user) internal pure returns (bytes32) {
        return bytes32(
            uint256(keccak256(abi.encode(user, keccak256(abi.encode(id, POSITION_SLOT))))) + SUPPLY_SHARES_OFFSET
        );
    }

    function positionBorrowSharesAndCollateralSlot(Id id, address user) internal pure returns (bytes32) {
        return bytes32(
            uint256(keccak256(abi.encode(user, keccak256(abi.encode(id, POSITION_SLOT)))))
                + BORROW_SHARES_AND_COLLATERAL_OFFSET
        );
    }

    function marketTotalSupplyAssetsAndSharesSlot(Id id) internal pure returns (bytes32) {
        return bytes32(uint256(keccak256(abi.encode(id, MARKET_SLOT))) + TOTAL_SUPPLY_ASSETS_AND_SHARES_OFFSET);
    }

    function marketTotalBorrowAssetsAndSharesSlot(Id id) internal pure returns (bytes32) {
        return bytes32(uint256(keccak256(abi.encode(id, MARKET_SLOT))) + TOTAL_BORROW_ASSETS_AND_SHARES_OFFSET);
    }

    function marketLastUpdateAndFeeSlot(Id id) internal pure returns (bytes32) {
        return bytes32(uint256(keccak256(abi.encode(id, MARKET_SLOT))) + LAST_UPDATE_AND_FEE_OFFSET);
    }

    function isIrmEnabledSlot(address irm) internal pure returns (bytes32) {
        return keccak256(abi.encode(irm, IS_IRM_ENABLED_SLOT));
    }

    function isLltvEnabledSlot(uint256 lltv) internal pure returns (bytes32) {
        return keccak256(abi.encode(lltv, IS_LLTV_ENABLED_SLOT));
    }

    function isAuthorizedSlot(address authorizer, address authorizee) internal pure returns (bytes32) {
        return keccak256(abi.encode(authorizee, keccak256(abi.encode(authorizer, IS_AUTHORIZED_SLOT))));
    }

    function nonceSlot(address authorizer) internal pure returns (bytes32) {
        return keccak256(abi.encode(authorizer, NONCE_SLOT));
    }

    function idToLoanTokenSlot(Id id) internal pure returns (bytes32) {
        return bytes32(uint256(keccak256(abi.encode(id, ID_TO_MARKET_PARAMS_SLOT))) + LOAN_TOKEN_OFFSET);
    }

    function idToCollateralTokenSlot(Id id) internal pure returns (bytes32) {
        return bytes32(uint256(keccak256(abi.encode(id, ID_TO_MARKET_PARAMS_SLOT))) + COLLATERAL_TOKEN_OFFSET);
    }

    function idToOracleSlot(Id id) internal pure returns (bytes32) {
        return bytes32(uint256(keccak256(abi.encode(id, ID_TO_MARKET_PARAMS_SLOT))) + ORACLE_OFFSET);
    }

    function idToIrmSlot(Id id) internal pure returns (bytes32) {
        return bytes32(uint256(keccak256(abi.encode(id, ID_TO_MARKET_PARAMS_SLOT))) + IRM_OFFSET);
    }

    function idToLltvSlot(Id id) internal pure returns (bytes32) {
        return bytes32(uint256(keccak256(abi.encode(id, ID_TO_MARKET_PARAMS_SLOT))) + LLTV_OFFSET);
    }
}

// node_modules/@openzeppelin/contracts/access/Ownable.sol

// OpenZeppelin Contracts (last updated v4.9.0) (access/Ownable.sol)

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        _transferOwnership(_msgSender());
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        _checkOwner();
        _;
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if the sender is not the owner.
     */
    function _checkOwner() internal view virtual {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby disabling any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}

// node_modules/@openzeppelin/contracts/token/ERC20/extensions/IERC20Metadata.sol

// OpenZeppelin Contracts v4.4.1 (token/ERC20/extensions/IERC20Metadata.sol)

/**
 * @dev Interface for the optional metadata functions from the ERC20 standard.
 *
 * _Available since v4.1._
 */
interface IERC20Metadata is IERC20 {
    /**
     * @dev Returns the name of the token.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the symbol of the token.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the decimals places of the token.
     */
    function decimals() external view returns (uint8);
}

// node_modules/@morpho-org/morpho-blue/src/libraries/periphery/MorphoLib.sol

/// @title MorphoLib
/// @author Morpho Labs
/// @custom:contact security@morpho.org
/// @notice Helper library to access Morpho storage variables.
/// @dev Warning: Supply and borrow getters may return outdated values that do not include accrued interest.
library MorphoLib {
    function supplyShares(IMorpho morpho, Id id, address user) internal view returns (uint256) {
        bytes32[] memory slot = _array(MorphoStorageLib.positionSupplySharesSlot(id, user));
        return uint256(morpho.extSloads(slot)[0]);
    }

    function borrowShares(IMorpho morpho, Id id, address user) internal view returns (uint256) {
        bytes32[] memory slot = _array(MorphoStorageLib.positionBorrowSharesAndCollateralSlot(id, user));
        return uint128(uint256(morpho.extSloads(slot)[0]));
    }

    function collateral(IMorpho morpho, Id id, address user) internal view returns (uint256) {
        bytes32[] memory slot = _array(MorphoStorageLib.positionBorrowSharesAndCollateralSlot(id, user));
        return uint256(morpho.extSloads(slot)[0] >> 128);
    }

    function totalSupplyAssets(IMorpho morpho, Id id) internal view returns (uint256) {
        bytes32[] memory slot = _array(MorphoStorageLib.marketTotalSupplyAssetsAndSharesSlot(id));
        return uint128(uint256(morpho.extSloads(slot)[0]));
    }

    function totalSupplyShares(IMorpho morpho, Id id) internal view returns (uint256) {
        bytes32[] memory slot = _array(MorphoStorageLib.marketTotalSupplyAssetsAndSharesSlot(id));
        return uint256(morpho.extSloads(slot)[0] >> 128);
    }

    function totalBorrowAssets(IMorpho morpho, Id id) internal view returns (uint256) {
        bytes32[] memory slot = _array(MorphoStorageLib.marketTotalBorrowAssetsAndSharesSlot(id));
        return uint128(uint256(morpho.extSloads(slot)[0]));
    }

    function totalBorrowShares(IMorpho morpho, Id id) internal view returns (uint256) {
        bytes32[] memory slot = _array(MorphoStorageLib.marketTotalBorrowAssetsAndSharesSlot(id));
        return uint256(morpho.extSloads(slot)[0] >> 128);
    }

    function lastUpdate(IMorpho morpho, Id id) internal view returns (uint256) {
        bytes32[] memory slot = _array(MorphoStorageLib.marketLastUpdateAndFeeSlot(id));
        return uint128(uint256(morpho.extSloads(slot)[0]));
    }

    function fee(IMorpho morpho, Id id) internal view returns (uint256) {
        bytes32[] memory slot = _array(MorphoStorageLib.marketLastUpdateAndFeeSlot(id));
        return uint256(morpho.extSloads(slot)[0] >> 128);
    }

    function _array(bytes32 x) private pure returns (bytes32[] memory) {
        bytes32[] memory res = new bytes32[](1);
        res[0] = x;
        return res;
    }
}

// node_modules/@openzeppelin/contracts/token/ERC20/ERC20.sol

// OpenZeppelin Contracts (last updated v4.9.0) (token/ERC20/ERC20.sol)

/**
 * @dev Implementation of the {IERC20} interface.
 *
 * This implementation is agnostic to the way tokens are created. This means
 * that a supply mechanism has to be added in a derived contract using {_mint}.
 * For a generic mechanism see {ERC20PresetMinterPauser}.
 *
 * TIP: For a detailed writeup see our guide
 * https://forum.openzeppelin.com/t/how-to-implement-erc20-supply-mechanisms/226[How
 * to implement supply mechanisms].
 *
 * The default value of {decimals} is 18. To change this, you should override
 * this function so it returns a different value.
 *
 * We have followed general OpenZeppelin Contracts guidelines: functions revert
 * instead returning `false` on failure. This behavior is nonetheless
 * conventional and does not conflict with the expectations of ERC20
 * applications.
 *
 * Additionally, an {Approval} event is emitted on calls to {transferFrom}.
 * This allows applications to reconstruct the allowance for all accounts just
 * by listening to said events. Other implementations of the EIP may not emit
 * these events, as it isn't required by the specification.
 *
 * Finally, the non-standard {decreaseAllowance} and {increaseAllowance}
 * functions have been added to mitigate the well-known issues around setting
 * allowances. See {IERC20-approve}.
 */
contract ERC20 is Context, IERC20, IERC20Metadata {
    mapping(address => uint256) private _balances;

    mapping(address => mapping(address => uint256)) private _allowances;

    uint256 private _totalSupply;

    string private _name;
    string private _symbol;

    /**
     * @dev Sets the values for {name} and {symbol}.
     *
     * All two of these values are immutable: they can only be set once during
     * construction.
     */
    constructor(string memory name_, string memory symbol_) {
        _name = name_;
        _symbol = symbol_;
    }

    /**
     * @dev Returns the name of the token.
     */
    function name() public view virtual override returns (string memory) {
        return _name;
    }

    /**
     * @dev Returns the symbol of the token, usually a shorter version of the
     * name.
     */
    function symbol() public view virtual override returns (string memory) {
        return _symbol;
    }

    /**
     * @dev Returns the number of decimals used to get its user representation.
     * For example, if `decimals` equals `2`, a balance of `505` tokens should
     * be displayed to a user as `5.05` (`505 / 10 ** 2`).
     *
     * Tokens usually opt for a value of 18, imitating the relationship between
     * Ether and Wei. This is the default value returned by this function, unless
     * it's overridden.
     *
     * NOTE: This information is only used for _display_ purposes: it in
     * no way affects any of the arithmetic of the contract, including
     * {IERC20-balanceOf} and {IERC20-transfer}.
     */
    function decimals() public view virtual override returns (uint8) {
        return 18;
    }

    /**
     * @dev See {IERC20-totalSupply}.
     */
    function totalSupply() public view virtual override returns (uint256) {
        return _totalSupply;
    }

    /**
     * @dev See {IERC20-balanceOf}.
     */
    function balanceOf(address account) public view virtual override returns (uint256) {
        return _balances[account];
    }

    /**
     * @dev See {IERC20-transfer}.
     *
     * Requirements:
     *
     * - `to` cannot be the zero address.
     * - the caller must have a balance of at least `amount`.
     */
    function transfer(address to, uint256 amount) public virtual override returns (bool) {
        address owner = _msgSender();
        _transfer(owner, to, amount);
        return true;
    }

    /**
     * @dev See {IERC20-allowance}.
     */
    function allowance(address owner, address spender) public view virtual override returns (uint256) {
        return _allowances[owner][spender];
    }

    /**
     * @dev See {IERC20-approve}.
     *
     * NOTE: If `amount` is the maximum `uint256`, the allowance is not updated on
     * `transferFrom`. This is semantically equivalent to an infinite approval.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function approve(address spender, uint256 amount) public virtual override returns (bool) {
        address owner = _msgSender();
        _approve(owner, spender, amount);
        return true;
    }

    /**
     * @dev See {IERC20-transferFrom}.
     *
     * Emits an {Approval} event indicating the updated allowance. This is not
     * required by the EIP. See the note at the beginning of {ERC20}.
     *
     * NOTE: Does not update the allowance if the current allowance
     * is the maximum `uint256`.
     *
     * Requirements:
     *
     * - `from` and `to` cannot be the zero address.
     * - `from` must have a balance of at least `amount`.
     * - the caller must have allowance for ``from``'s tokens of at least
     * `amount`.
     */
    function transferFrom(address from, address to, uint256 amount) public virtual override returns (bool) {
        address spender = _msgSender();
        _spendAllowance(from, spender, amount);
        _transfer(from, to, amount);
        return true;
    }

    /**
     * @dev Atomically increases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function increaseAllowance(address spender, uint256 addedValue) public virtual returns (bool) {
        address owner = _msgSender();
        _approve(owner, spender, allowance(owner, spender) + addedValue);
        return true;
    }

    /**
     * @dev Atomically decreases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `spender` must have allowance for the caller of at least
     * `subtractedValue`.
     */
    function decreaseAllowance(address spender, uint256 subtractedValue) public virtual returns (bool) {
        address owner = _msgSender();
        uint256 currentAllowance = allowance(owner, spender);
        require(currentAllowance >= subtractedValue, "ERC20: decreased allowance below zero");
        unchecked {
            _approve(owner, spender, currentAllowance - subtractedValue);
        }

        return true;
    }

    /**
     * @dev Moves `amount` of tokens from `from` to `to`.
     *
     * This internal function is equivalent to {transfer}, and can be used to
     * e.g. implement automatic token fees, slashing mechanisms, etc.
     *
     * Emits a {Transfer} event.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `to` cannot be the zero address.
     * - `from` must have a balance of at least `amount`.
     */
    function _transfer(address from, address to, uint256 amount) internal virtual {
        require(from != address(0), "ERC20: transfer from the zero address");
        require(to != address(0), "ERC20: transfer to the zero address");

        _beforeTokenTransfer(from, to, amount);

        uint256 fromBalance = _balances[from];
        require(fromBalance >= amount, "ERC20: transfer amount exceeds balance");
        unchecked {
            _balances[from] = fromBalance - amount;
            // Overflow not possible: the sum of all balances is capped by totalSupply, and the sum is preserved by
            // decrementing then incrementing.
            _balances[to] += amount;
        }

        emit Transfer(from, to, amount);

        _afterTokenTransfer(from, to, amount);
    }

    /** @dev Creates `amount` tokens and assigns them to `account`, increasing
     * the total supply.
     *
     * Emits a {Transfer} event with `from` set to the zero address.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     */
    function _mint(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: mint to the zero address");

        _beforeTokenTransfer(address(0), account, amount);

        _totalSupply += amount;
        unchecked {
            // Overflow not possible: balance + amount is at most totalSupply + amount, which is checked above.
            _balances[account] += amount;
        }
        emit Transfer(address(0), account, amount);

        _afterTokenTransfer(address(0), account, amount);
    }

    /**
     * @dev Destroys `amount` tokens from `account`, reducing the
     * total supply.
     *
     * Emits a {Transfer} event with `to` set to the zero address.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     * - `account` must have at least `amount` tokens.
     */
    function _burn(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: burn from the zero address");

        _beforeTokenTransfer(account, address(0), amount);

        uint256 accountBalance = _balances[account];
        require(accountBalance >= amount, "ERC20: burn amount exceeds balance");
        unchecked {
            _balances[account] = accountBalance - amount;
            // Overflow not possible: amount <= accountBalance <= totalSupply.
            _totalSupply -= amount;
        }

        emit Transfer(account, address(0), amount);

        _afterTokenTransfer(account, address(0), amount);
    }

    /**
     * @dev Sets `amount` as the allowance of `spender` over the `owner` s tokens.
     *
     * This internal function is equivalent to `approve`, and can be used to
     * e.g. set automatic allowances for certain subsystems, etc.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `owner` cannot be the zero address.
     * - `spender` cannot be the zero address.
     */
    function _approve(address owner, address spender, uint256 amount) internal virtual {
        require(owner != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");

        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }

    /**
     * @dev Updates `owner` s allowance for `spender` based on spent `amount`.
     *
     * Does not update the allowance amount in case of infinite allowance.
     * Revert if not enough allowance is available.
     *
     * Might emit an {Approval} event.
     */
    function _spendAllowance(address owner, address spender, uint256 amount) internal virtual {
        uint256 currentAllowance = allowance(owner, spender);
        if (currentAllowance != type(uint256).max) {
            require(currentAllowance >= amount, "ERC20: insufficient allowance");
            unchecked {
                _approve(owner, spender, currentAllowance - amount);
            }
        }
    }

    /**
     * @dev Hook that is called before any transfer of tokens. This includes
     * minting and burning.
     *
     * Calling conditions:
     *
     * - when `from` and `to` are both non-zero, `amount` of ``from``'s tokens
     * will be transferred to `to`.
     * - when `from` is zero, `amount` tokens will be minted for `to`.
     * - when `to` is zero, `amount` of ``from``'s tokens will be burned.
     * - `from` and `to` are never both zero.
     *
     * To learn more about hooks, head to xref:ROOT:extending-contracts.adoc#using-hooks[Using Hooks].
     */
    function _beforeTokenTransfer(address from, address to, uint256 amount) internal virtual {}

    /**
     * @dev Hook that is called after any transfer of tokens. This includes
     * minting and burning.
     *
     * Calling conditions:
     *
     * - when `from` and `to` are both non-zero, `amount` of ``from``'s tokens
     * has been transferred to `to`.
     * - when `from` is zero, `amount` tokens have been minted for `to`.
     * - when `to` is zero, `amount` of ``from``'s tokens have been burned.
     * - `from` and `to` are never both zero.
     *
     * To learn more about hooks, head to xref:ROOT:extending-contracts.adoc#using-hooks[Using Hooks].
     */
    function _afterTokenTransfer(address from, address to, uint256 amount) internal virtual {}
}

// node_modules/@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol

// OpenZeppelin Contracts (last updated v4.9.3) (token/ERC20/utils/SafeERC20.sol)

/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using Address for address;

    /**
     * @dev Transfer `value` amount of `token` from the calling contract to `to`. If `token` returns no value,
     * non-reverting calls are assumed to be successful.
     */
    function safeTransfer(IERC20 token, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    /**
     * @dev Transfer `value` amount of `token` from `from` to `to`, spending the approval given by `from` to the
     * calling contract. If `token` returns no value, non-reverting calls are assumed to be successful.
     */
    function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(IERC20 token, address spender, uint256 value) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        require(
            (value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    /**
     * @dev Increase the calling contract's allowance toward `spender` by `value`. If `token` returns no value,
     * non-reverting calls are assumed to be successful.
     */
    function safeIncreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 oldAllowance = token.allowance(address(this), spender);
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, oldAllowance + value));
    }

    /**
     * @dev Decrease the calling contract's allowance toward `spender` by `value`. If `token` returns no value,
     * non-reverting calls are assumed to be successful.
     */
    function safeDecreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        unchecked {
            uint256 oldAllowance = token.allowance(address(this), spender);
            require(oldAllowance >= value, "SafeERC20: decreased allowance below zero");
            _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, oldAllowance - value));
        }
    }

    /**
     * @dev Set the calling contract's allowance toward `spender` to `value`. If `token` returns no value,
     * non-reverting calls are assumed to be successful. Meant to be used with tokens that require the approval
     * to be set to zero before setting it to a non-zero value, such as USDT.
     */
    function forceApprove(IERC20 token, address spender, uint256 value) internal {
        bytes memory approvalCall = abi.encodeWithSelector(token.approve.selector, spender, value);

        if (!_callOptionalReturnBool(token, approvalCall)) {
            _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, 0));
            _callOptionalReturn(token, approvalCall);
        }
    }

    /**
     * @dev Use a ERC-2612 signature to set the `owner` approval toward `spender` on `token`.
     * Revert on invalid signature.
     */
    function safePermit(
        IERC20Permit token,
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal {
        uint256 nonceBefore = token.nonces(owner);
        token.permit(owner, spender, value, deadline, v, r, s);
        uint256 nonceAfter = token.nonces(owner);
        require(nonceAfter == nonceBefore + 1, "SafeERC20: permit did not succeed");
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address-functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        require(returndata.length == 0 || abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     *
     * This is a variant of {_callOptionalReturn} that silents catches all reverts and returns a bool instead.
     */
    function _callOptionalReturnBool(IERC20 token, bytes memory data) private returns (bool) {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We cannot use {Address-functionCall} here since this should return false
        // and not revert is the subcall reverts.

        (bool success, bytes memory returndata) = address(token).call(data);
        return
            success && (returndata.length == 0 || abi.decode(returndata, (bool))) && Address.isContract(address(token));
    }
}

// node_modules/@morpho-org/morpho-blue/src/libraries/periphery/MorphoBalancesLib.sol

/// @title MorphoBalancesLib
/// @author Morpho Labs
/// @custom:contact security@morpho.org
/// @notice Helper library exposing getters with the expected value after interest accrual.
/// @dev This library is not used in Morpho itself and is intended to be used by integrators.
/// @dev The getter to retrieve the expected total borrow shares is not exposed because interest accrual does not apply
/// to it. The value can be queried directly on Morpho using `totalBorrowShares`.
library MorphoBalancesLib {
    using MathLib for uint256;
    using MathLib for uint128;
    using UtilsLib for uint256;
    using MorphoLib for IMorpho;
    using SharesMathLib for uint256;
    using MarketParamsLib for MarketParams;

    /// @notice Returns the expected market balances of a market after having accrued interest.
    /// @return The expected total supply assets.
    /// @return The expected total supply shares.
    /// @return The expected total borrow assets.
    /// @return The expected total borrow shares.
    function expectedMarketBalances(IMorpho morpho, MarketParams memory marketParams)
        internal
        view
        returns (uint256, uint256, uint256, uint256)
    {
        Id id = marketParams.id();
        Market memory market = morpho.market(id);

        uint256 elapsed = block.timestamp - market.lastUpdate;

        // Skipped if elapsed == 0 or totalBorrowAssets == 0 because interest would be null, or if irm == address(0).
        if (elapsed != 0 && market.totalBorrowAssets != 0 && marketParams.irm != address(0)) {
            uint256 borrowRate = IIrm(marketParams.irm).borrowRateView(marketParams, market);
            uint256 interest = market.totalBorrowAssets.wMulDown(borrowRate.wTaylorCompounded(elapsed));
            market.totalBorrowAssets += interest.toUint128();
            market.totalSupplyAssets += interest.toUint128();

            if (market.fee != 0) {
                uint256 feeAmount = interest.wMulDown(market.fee);
                // The fee amount is subtracted from the total supply in this calculation to compensate for the fact
                // that total supply is already updated.
                uint256 feeShares =
                    feeAmount.toSharesDown(market.totalSupplyAssets - feeAmount, market.totalSupplyShares);
                market.totalSupplyShares += feeShares.toUint128();
            }
        }

        return (market.totalSupplyAssets, market.totalSupplyShares, market.totalBorrowAssets, market.totalBorrowShares);
    }

    /// @notice Returns the expected total supply assets of a market after having accrued interest.
    function expectedTotalSupplyAssets(IMorpho morpho, MarketParams memory marketParams)
        internal
        view
        returns (uint256 totalSupplyAssets)
    {
        (totalSupplyAssets,,,) = expectedMarketBalances(morpho, marketParams);
    }

    /// @notice Returns the expected total borrow assets of a market after having accrued interest.
    function expectedTotalBorrowAssets(IMorpho morpho, MarketParams memory marketParams)
        internal
        view
        returns (uint256 totalBorrowAssets)
    {
        (,, totalBorrowAssets,) = expectedMarketBalances(morpho, marketParams);
    }

    /// @notice Returns the expected total supply shares of a market after having accrued interest.
    function expectedTotalSupplyShares(IMorpho morpho, MarketParams memory marketParams)
        internal
        view
        returns (uint256 totalSupplyShares)
    {
        (, totalSupplyShares,,) = expectedMarketBalances(morpho, marketParams);
    }

    /// @notice Returns the expected supply assets balance of `user` on a market after having accrued interest.
    /// @dev Warning: Wrong for `feeRecipient` because their supply shares increase is not taken into account.
    /// @dev Warning: Withdrawing using the expected supply assets can lead to a revert due to conversion roundings from
    /// assets to shares.
    function expectedSupplyAssets(IMorpho morpho, MarketParams memory marketParams, address user)
        internal
        view
        returns (uint256)
    {
        Id id = marketParams.id();
        uint256 supplyShares = morpho.supplyShares(id, user);
        (uint256 totalSupplyAssets, uint256 totalSupplyShares,,) = expectedMarketBalances(morpho, marketParams);

        return supplyShares.toAssetsDown(totalSupplyAssets, totalSupplyShares);
    }

    /// @notice Returns the expected borrow assets balance of `user` on a market after having accrued interest.
    /// @dev Warning: The expected balance is rounded up, so it may be greater than the market's expected total borrow
    /// assets.
    function expectedBorrowAssets(IMorpho morpho, MarketParams memory marketParams, address user)
        internal
        view
        returns (uint256)
    {
        Id id = marketParams.id();
        uint256 borrowShares = morpho.borrowShares(id, user);
        (,, uint256 totalBorrowAssets, uint256 totalBorrowShares) = expectedMarketBalances(morpho, marketParams);

        return borrowShares.toAssetsUp(totalBorrowAssets, totalBorrowShares);
    }
}

// contracts/core/strategies/StrategySupplyBase.sol

/**
 * @title Strategy Supply Base is a base contract for strategies that can deploy or
 * undeploy assets
 *
 * @author Chef Nil <duarte@bakerfi.xyz>
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 *
 * @notice A simple strategy that can deploy or undeploy assets to a lending pool
 */
abstract contract StrategySupplyBase is IStrategy, ReentrancyGuard, Ownable {
    using SafeERC20 for ERC20;
    using MathLibrary for uint256;

    error FailedToApproveAllowanceForAAVE();
    error ZeroAddress();
    error ZeroAmount();
    error InsufficientBalance();
    error WithdrawalValueMismatch();

    // The asset being managed
    address internal immutable _asset;

    // The amount of the asset that was successfully deployed
    uint256 private _deployedAmount;

    /**
     * @param asset_ The address of the asset to be managed
     */
    constructor(address initialOwner, address asset_) ReentrancyGuard() Ownable() {
        if (initialOwner == address(0) || asset_ == address(0)) revert ZeroAddress();

        _asset = asset_;
        _transferOwnership(initialOwner);
    }
    /**
     * @notice Deploys a specified amount of the managed asset to the lending pool.
     * @param amount The amount of the asset to be deployed.
     * @return The amount of the asset that was successfully deployed.
     */
    function _deploy(uint256 amount) internal virtual returns (uint256);

    /**
     * @notice Undeploys a specified amount of the managed asset from the lending pool.
     * @param amount The amount of the asset to be undeployed.
     * @return The amount of the asset that was successfully undeployed.
     */
    function _undeploy(uint256 amount) internal virtual returns (uint256);

    /**
     * @notice Retrieves the current balance of the managed asset in the lending pool.
     * @dev This function does not perform any conversion to USD.
     * @return The current balance of the managed asset.
     */
    function _getBalance() internal view virtual returns (uint256);

    /**
     * @inheritdoc IStrategy
     */
    function deploy(uint256 amount) external nonReentrant onlyOwner returns (uint256 deployedAmount) {
        if (amount == 0) revert ZeroAmount();

        // Transfer assets from user
        ERC20(_asset).safeTransferFrom(msg.sender, address(this), amount);

        // Transfer assets from caller to strategy
        deployedAmount = _deploy(amount);

        _deployedAmount += deployedAmount;

        emit StrategyDeploy(msg.sender, deployedAmount);

        emit StrategyAmountUpdate(_deployedAmount);

        return deployedAmount;
    }

    /**
     * @inheritdoc IStrategy
     */
    function harvest() external returns (int256 balanceChange) {
        // Get Balance
        uint256 newBalance = getBalance();

        balanceChange = int256(newBalance) - int256(_deployedAmount);

        if (balanceChange > 0) {
            emit StrategyProfit(uint256(balanceChange));
        } else if (balanceChange < 0) {
            emit StrategyLoss(uint256(-balanceChange));
        }
        if (balanceChange != 0) {
            emit StrategyAmountUpdate(newBalance);
        }
        _deployedAmount = newBalance;
    }

    /**
     * @inheritdoc IStrategy
     */
    function undeploy(uint256 amount) external nonReentrant onlyOwner returns (uint256 undeployedAmount) {
        if (amount == 0) revert ZeroAmount();

        // Get Balance
        uint256 balance = getBalance();
        if (amount > balance) revert InsufficientBalance();

        // Transfer assets back to caller
        uint256 withdrawalValue = _undeploy(amount);

        // Check withdrawal value matches the initial amount
        // Transfer assets to user
        ERC20(_asset).safeTransfer(msg.sender, withdrawalValue);

        balance -= amount;
        emit StrategyUndeploy(msg.sender, withdrawalValue);
        emit StrategyAmountUpdate(balance);

        return amount;
    }

    /**
     * @inheritdoc IStrategy
     */
    function totalAssets() external view returns (uint256) {
        return getBalance();
    }

    /**
     * @inheritdoc IStrategy
     */
    function asset() external view returns (address) {
        return _asset;
    }

    /**
     * Get the Current Balance on AAVEv3
     *
     * @dev !Important: No Conversion to USD Done
     */
    function getBalance() public view virtual returns (uint256) {
        return _getBalance();
    }
}

// contracts/core/strategies/StrategySupplyMorpho.sol

/**
 * @title Strategy Supply Morpho 🅿️
 *
 * @author Chef Nil <duarte@bakerfi.xyz>
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 *
 * @notice A simple strategy that can deploy or undeploy assets to Morpho
 */
contract StrategySupplyMorpho is StrategySupplyBase {
    using SafeERC20 for ERC20;
    using SharesMathLib for uint256;
    using MarketParamsLib for MarketParams;
    using MorphoLib for IMorpho;
    using MorphoBalancesLib for IMorpho;

    error FailedToApproveAllowanceForMorpho();
    error InvalidMorphoBlueContract();

    MarketParams private _marketParams; // Parameters related to the market for the strategy.
    /// @notice Instance of the Morpho protocol interface.
    IMorpho private immutable _morpho;

    /// @param initialOwner The address of the initial owner of the contract.
    /// @param asset_ The address of the asset to be managed.
    /// @param morphoBlue The address of the Morpho protocol contract.
    /// @param morphoMarketId The market ID for the Morpho market.
    /// @dev Reverts if the morphoBlue address is zero or if the Morpho contract is invalid.
    constructor(
        address initialOwner,
        address asset_,
        address morphoBlue,
        Id morphoMarketId
    ) StrategySupplyBase(initialOwner, asset_) {
        if (morphoBlue == address(0)) revert ZeroAddress();

        _morpho = IMorpho(morphoBlue);

        if (address(_morpho) == address(0)) revert InvalidMorphoBlueContract();

        _marketParams = _morpho.idToMarketParams(morphoMarketId);

        // Allowance approval
        if (!ERC20(asset_).approve(morphoBlue, type(uint256).max)) {
            revert FailedToApproveAllowanceForMorpho();
        }
    }

    /// @notice Deploys a specified amount of the managed asset to the Morpho protocol.
    /// @param amount The amount of the asset to be deployed.
    /// @return deployedAmount The amount of the asset that was successfully deployed.
    function _deploy(uint256 amount) internal override returns (uint256) {
        (uint256 deployedAmount, ) = _morpho.supply(_marketParams, amount, 0, address(this), hex"");
        return deployedAmount;
    }

    /// @notice Undeploys a specified amount of the managed asset from the Morpho protocol.
    /// @param amount The amount of the asset to be undeployed.
    /// @return withdrawalValue The amount of the asset that was successfully undeployed.
    function _undeploy(uint256 amount) internal override returns (uint256) {
        Id id = _marketParams.id();
        uint256 assetsWithdrawn = 0;
        uint256 totalSupplyAssets = _morpho.totalSupplyAssets(id);
        uint256 totalSupplyShares = _morpho.totalSupplyShares(id);

        uint256 shares = _morpho.supplyShares(id, address(this));
        uint256 assetsMax = shares.toAssetsDown(totalSupplyAssets, totalSupplyShares);

        if (amount >= assetsMax) {
            (assetsWithdrawn, ) = _morpho.withdraw(_marketParams, 0, shares, address(this), address(this));
        } else {
            (assetsWithdrawn, ) = _morpho.withdraw(_marketParams, amount, 0, address(this), address(this));
        }

        return assetsWithdrawn;
    }

    /// @notice Retrieves the current balance of the managed asset in the Morpho protocol.
    /// @return The current balance of the managed asset.
    function _getBalance() internal view override returns (uint256) {
        return _morpho.expectedSupplyAssets(_marketParams, address(this));
    }
}

