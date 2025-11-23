// SPDX-License-Identifier: BUSL-1.1
pragma solidity >=0.6.2 >=0.7.5 ^0.8.0 ^0.8.1 ^0.8.2 ^0.8.24;

// contracts/core/Constants.sol

/**
 * @title These are global constants used by other contracts
 */

/**
 * @dev Constant representing the maximum allowed loan-to-value ratio.
 *
 * This constant holds the value 1e9, representing the maximum allowed loan-to-value ratio as 100%.
 * It is used to limit the loan-to-value ratio for specific processes.
 */
uint256 constant MAX_LOAN_TO_VALUE = 1e9; // 100%
/**
 * @dev Constant representing the maximum allowed number of loops.
 *
 * This constant holds the value 20, representing the maximum allowed number of loops.
 * It is used to limit the number of loops for a specific process.
 */
uint8 constant MAX_LOOPS = 20; // 100%
/**
 * @dev Constant representing the precision for percentage values.
 *
 * This constant holds the value 1e9, representing the precision for percentage values.
 * It is used for calculations involving percentage precision.
 */
uint256 constant PERCENTAGE_PRECISION = 1e9;
address constant ETH = 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE;
uint8 constant SYSTEM_DECIMALS = 18;

bytes32 constant ADMIN_ROLE = 0x00;
bytes32 constant PAUSER_ROLE = keccak256("PAUSER_ROLE");
bytes32 constant VAULT_MANAGER_ROLE = keccak256("VAULT_MANAGER_ROLE");

// contracts/core/EmptySlot.sol

contract EmptySlot {
    uint256 private _emptySlot;
}

// contracts/interfaces/aerodrome/ISwapRouter.sol

pragma abicoder v2;

/// @title Callback for ICLPoolActions#swap
/// @notice Any contract that calls ICLPoolActions#swap must implement this interface
interface ICLSwapCallback {
    /// @notice Called to `msg.sender` after executing a swap via ICLPool#swap.
    /// @dev In the implementation you must pay the pool tokens owed for the swap.
    /// The caller of this method must be checked to be a CLPool deployed by the canonical CLFactory.
    /// amount0Delta and amount1Delta can both be 0 if no tokens were swapped.
    /// @param amount0Delta The amount of token0 that was sent (negative) or must be received (positive) by the pool by
    /// the end of the swap. If positive, the callback must send that amount of token0 to the pool.
    /// @param amount1Delta The amount of token1 that was sent (negative) or must be received (positive) by the pool by
    /// the end of the swap. If positive, the callback must send that amount of token1 to the pool.
    /// @param data Any data passed through by the caller via the ICLPoolActions#swap call
    function uniswapV3SwapCallback(int256 amount0Delta, int256 amount1Delta, bytes calldata data) external;
}

/// @title Router token swapping functionality
/// @notice Functions for swapping tokens via CL
interface ISwapRouter is ICLSwapCallback {
    struct ExactInputSingleParams {
        address tokenIn;
        address tokenOut;
        int24 tickSpacing;
        address recipient;
        uint256 deadline;
        uint256 amountIn;
        uint256 amountOutMinimum;
        uint160 sqrtPriceLimitX96;
    }

    /// @notice Swaps `amountIn` of one token for as much as possible of another token
    /// @param params The parameters necessary for the swap, encoded as `ExactInputSingleParams` in calldata
    /// @return amountOut The amount of the received token
    function exactInputSingle(ExactInputSingleParams calldata params) external payable returns (uint256 amountOut);

    struct ExactInputParams {
        bytes path;
        address recipient;
        uint256 deadline;
        uint256 amountIn;
        uint256 amountOutMinimum;
    }

    /// @notice Swaps `amountIn` of one token for as much as possible of another along the specified path
    /// @param params The parameters necessary for the multi-hop swap, encoded as `ExactInputParams` in calldata
    /// @return amountOut The amount of the received token
    function exactInput(ExactInputParams calldata params) external payable returns (uint256 amountOut);

    struct ExactOutputSingleParams {
        address tokenIn;
        address tokenOut;
        int24 tickSpacing;
        address recipient;
        uint256 deadline;
        uint256 amountOut;
        uint256 amountInMaximum;
        uint160 sqrtPriceLimitX96;
    }

    /// @notice Swaps as little as possible of one token for `amountOut` of another token
    /// @param params The parameters necessary for the swap, encoded as `ExactOutputSingleParams` in calldata
    /// @return amountIn The amount of the input token
    function exactOutputSingle(ExactOutputSingleParams calldata params) external payable returns (uint256 amountIn);

    struct ExactOutputParams {
        bytes path;
        address recipient;
        uint256 deadline;
        uint256 amountOut;
        uint256 amountInMaximum;
    }

    /// @notice Swaps as little as possible of one token for `amountOut` of another along the specified path (reversed)
    /// @param params The parameters necessary for the multi-hop swap, encoded as `ExactOutputParams` in calldata
    /// @return amountIn The amount of the input token
    function exactOutput(ExactOutputParams calldata params) external payable returns (uint256 amountIn);
}

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

// contracts/interfaces/core/IStrategySettings.sol

/**
 * @title Bakerfi Settings Interface
 *
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 * @author Chef Kal-EL <chef.kal-el@bakerfi.xyz>
 *
 * @dev The Settings contract have to implement this interface
 *
 */
interface IStrategySettings {
    /**
     * @dev Emitted when the price max age is changed
     * @param value The new price max age
     */
    event PriceMaxAgeChanged(uint256 indexed value);

    /**
     * @dev Emitted when the price max conf is changed
     * @param value The new price max conf
     */
    event PriceMaxConfChanged(uint256 indexed value);

    /**
     * @notice Sets the maximum age of the price data.
     * @param value The maximum age in seconds.
     */
    function setPriceMaxAge(uint256 value) external;

    /**
     * @notice Retrieves the maximum age of the price data.
     * @return The maximum age in seconds.
     */
    function getPriceMaxAge() external view returns (uint256);

    /**
     * @notice Sets the maximum confidence level for the price data in percentage
     * @param value The maximum confidence level.
     */
    function setPriceMaxConf(uint256 value) external;

    /**
     * @notice Retrieves the maximum confidence level for the price data.
     * @return The maximum confidence level.
     */
    function getPriceMaxConf() external view returns (uint256);
}

// contracts/interfaces/core/ISwapHandler.sol

/**
 * @title Generic Swapper Handler
 *
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 * @author Chef Kal-EL <chef.kal-el@bakerfi.xyz>
 *
 * @dev A contract that converts one token to another
 */
abstract contract ISwapHandler {
    error InvalidInputToken();
    error InvalidOutputToken();
    error SwapFailed();

    /// @notice Params for swaps using SwapHub contract and swap handlers
    /// @param underlyingIn sold token address
    /// @param underlyingOut bought token address
    /// @param mode type of the swap: 0 for exact input, 1 for exact output
    /// @param amountIn amount of token to sell. Exact value for exact input, maximum for exact output
    /// @param amountOut amount of token to buy. Exact value for exact output, minimum for exact input
    /// @param payload multi-purpose byte param. The usage depends on the swap handler implementation
    struct SwapParams {
        address underlyingIn;
        address underlyingOut;
        SwapType mode;
        uint256 amountIn;
        uint256 amountOut;
        bytes payload;
    }

    // @notice The type of swap
    enum SwapType {
        EXACT_INPUT,
        EXACT_OUTPUT
    }

    /// @notice Execute a trade on the swap handler
    /// @param params struct defining the requested trade
    function swap(SwapParams memory params) internal virtual returns (uint256 amountIn, uint256 amountOut);
}

// contracts/interfaces/uniswap/v2/IUniswapV2Router01.sol

interface IUniswapV2Router01 {
    function factory() external pure returns (address);
    function WETH() external pure returns (address);

    function addLiquidity(
        address tokenA,
        address tokenB,
        uint amountADesired,
        uint amountBDesired,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline
    ) external returns (uint amountA, uint amountB, uint liquidity);
    function addLiquidityETH(
        address token,
        uint amountTokenDesired,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external payable returns (uint amountToken, uint amountETH, uint liquidity);
    function removeLiquidity(
        address tokenA,
        address tokenB,
        uint liquidity,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline
    ) external returns (uint amountA, uint amountB);
    function removeLiquidityETH(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external returns (uint amountToken, uint amountETH);
    function removeLiquidityWithPermit(
        address tokenA,
        address tokenB,
        uint liquidity,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline,
        bool approveMax,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external returns (uint amountA, uint amountB);
    function removeLiquidityETHWithPermit(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline,
        bool approveMax,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external returns (uint amountToken, uint amountETH);
    function swapExactTokensForTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external returns (uint[] memory amounts);
    function swapTokensForExactTokens(
        uint amountOut,
        uint amountInMax,
        address[] calldata path,
        address to,
        uint deadline
    ) external returns (uint[] memory amounts);
    function swapExactETHForTokens(
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external payable returns (uint[] memory amounts);
    function swapTokensForExactETH(
        uint amountOut,
        uint amountInMax,
        address[] calldata path,
        address to,
        uint deadline
    ) external returns (uint[] memory amounts);
    function swapExactTokensForETH(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external returns (uint[] memory amounts);
    function swapETHForExactTokens(
        uint amountOut,
        address[] calldata path,
        address to,
        uint deadline
    ) external payable returns (uint[] memory amounts);

    function quote(uint amountA, uint reserveA, uint reserveB) external pure returns (uint amountB);
    function getAmountOut(uint amountIn, uint reserveIn, uint reserveOut) external pure returns (uint amountOut);
    function getAmountIn(uint amountOut, uint reserveIn, uint reserveOut) external pure returns (uint amountIn);
    function getAmountsOut(uint amountIn, address[] calldata path) external view returns (uint[] memory amounts);
    function getAmountsIn(uint amountOut, address[] calldata path) external view returns (uint[] memory amounts);
}

// contracts/interfaces/uniswap/v3/IV3SwapRouter.sol

// Adapted version from
// https://github.com/Uniswap/swap-router-contracts/blob/v1.1.0/contracts/interfaces/IV3SwapRouter.sol
// Using Uniswap Router 02

interface IUniswapV3SwapCallback {
    /// @notice Called to `msg.sender` after executing a swap via IUniswapV3Pool#swap.
    /// @dev In the implementation you must pay the pool tokens owed for the swap.
    /// The caller of this method must be checked to be a UniswapV3Pool deployed by the canonical UniswapV3Factory.
    /// amount0Delta and amount1Delta can both be 0 if no tokens were swapped.
    /// @param amount0Delta The amount of token0 that was sent (negative) or must be received (positive) by the pool by
    /// the end of the swap. If positive, the callback must send that amount of token0 to the pool.
    /// @param amount1Delta The amount of token1 that was sent (negative) or must be received (positive) by the pool by
    /// the end of the swap. If positive, the callback must send that amount of token1 to the pool.
    /// @param data Any data passed through by the caller via the IUniswapV3PoolActions#swap call
    function uniswapV3SwapCallback(int256 amount0Delta, int256 amount1Delta, bytes calldata data) external;
}

/// @title Router token swapping functionality
/// @notice Functions for swapping tokens via Uniswap V3
interface IV3SwapRouter is IUniswapV3SwapCallback {
    struct ExactInputSingleParams {
        address tokenIn;
        address tokenOut;
        uint24 fee;
        address recipient;
        uint256 amountIn;
        uint256 amountOutMinimum;
        uint160 sqrtPriceLimitX96;
    }

    /// @notice Swaps `amountIn` of one token for as much as possible of another token
    /// @param params The parameters necessary for the swap, encoded as `ExactInputSingleParams` in calldata
    /// @return amountOut The amount of the received token
    function exactInputSingle(ExactInputSingleParams calldata params) external payable returns (uint256 amountOut);

    struct ExactInputParams {
        bytes path;
        address recipient;
        uint256 amountIn;
        uint256 amountOutMinimum;
    }

    /// @notice Swaps `amountIn` of one token for as much as possible of another along the specified path
    /// @param params The parameters necessary for the multi-hop swap, encoded as `ExactInputParams` in calldata
    /// @return amountOut The amount of the received token
    function exactInput(ExactInputParams calldata params) external payable returns (uint256 amountOut);

    struct ExactOutputSingleParams {
        address tokenIn;
        address tokenOut;
        uint24 fee;
        address recipient;
        uint256 amountOut;
        uint256 amountInMaximum;
        uint160 sqrtPriceLimitX96;
    }

    /// @notice Swaps as little as possible of one token for `amountOut` of another token
    /// @param params The parameters necessary for the swap, encoded as `ExactOutputSingleParams` in calldata
    /// @return amountIn The amount of the input token
    function exactOutputSingle(ExactOutputSingleParams calldata params) external payable returns (uint256 amountIn);

    struct ExactOutputParams {
        bytes path;
        address recipient;
        uint256 amountOut;
        uint256 amountInMaximum;
    }

    /// @notice Swaps as little as possible of one token for `amountOut` of another along the specified path (reversed)
    /// @param params The parameters necessary for the multi-hop swap, encoded as `ExactOutputParams` in calldata
    /// @return amountIn The amount of the input token
    function exactOutput(ExactOutputParams calldata params) external payable returns (uint256 amountIn);
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

// node_modules/@openzeppelin/contracts/utils/structs/EnumerableSet.sol

// OpenZeppelin Contracts (last updated v4.9.0) (utils/structs/EnumerableSet.sol)
// This file was procedurally generated from scripts/generate/templates/EnumerableSet.js.

/**
 * @dev Library for managing
 * https://en.wikipedia.org/wiki/Set_(abstract_data_type)[sets] of primitive
 * types.
 *
 * Sets have the following properties:
 *
 * - Elements are added, removed, and checked for existence in constant time
 * (O(1)).
 * - Elements are enumerated in O(n). No guarantees are made on the ordering.
 *
 * ```solidity
 * contract Example {
 *     // Add the library methods
 *     using EnumerableSet for EnumerableSet.AddressSet;
 *
 *     // Declare a set state variable
 *     EnumerableSet.AddressSet private mySet;
 * }
 * ```
 *
 * As of v3.3.0, sets of type `bytes32` (`Bytes32Set`), `address` (`AddressSet`)
 * and `uint256` (`UintSet`) are supported.
 *
 * [WARNING]
 * ====
 * Trying to delete such a structure from storage will likely result in data corruption, rendering the structure
 * unusable.
 * See https://github.com/ethereum/solidity/pull/11843[ethereum/solidity#11843] for more info.
 *
 * In order to clean an EnumerableSet, you can either remove all elements one by one or create a fresh instance using an
 * array of EnumerableSet.
 * ====
 */
library EnumerableSet {
    // To implement this library for multiple types with as little code
    // repetition as possible, we write it in terms of a generic Set type with
    // bytes32 values.
    // The Set implementation uses private functions, and user-facing
    // implementations (such as AddressSet) are just wrappers around the
    // underlying Set.
    // This means that we can only create new EnumerableSets for types that fit
    // in bytes32.

    struct Set {
        // Storage of set values
        bytes32[] _values;
        // Position of the value in the `values` array, plus 1 because index 0
        // means a value is not in the set.
        mapping(bytes32 => uint256) _indexes;
    }

    /**
     * @dev Add a value to a set. O(1).
     *
     * Returns true if the value was added to the set, that is if it was not
     * already present.
     */
    function _add(Set storage set, bytes32 value) private returns (bool) {
        if (!_contains(set, value)) {
            set._values.push(value);
            // The value is stored at length-1, but we add 1 to all indexes
            // and use 0 as a sentinel value
            set._indexes[value] = set._values.length;
            return true;
        } else {
            return false;
        }
    }

    /**
     * @dev Removes a value from a set. O(1).
     *
     * Returns true if the value was removed from the set, that is if it was
     * present.
     */
    function _remove(Set storage set, bytes32 value) private returns (bool) {
        // We read and store the value's index to prevent multiple reads from the same storage slot
        uint256 valueIndex = set._indexes[value];

        if (valueIndex != 0) {
            // Equivalent to contains(set, value)
            // To delete an element from the _values array in O(1), we swap the element to delete with the last one in
            // the array, and then remove the last element (sometimes called as 'swap and pop').
            // This modifies the order of the array, as noted in {at}.

            uint256 toDeleteIndex = valueIndex - 1;
            uint256 lastIndex = set._values.length - 1;

            if (lastIndex != toDeleteIndex) {
                bytes32 lastValue = set._values[lastIndex];

                // Move the last value to the index where the value to delete is
                set._values[toDeleteIndex] = lastValue;
                // Update the index for the moved value
                set._indexes[lastValue] = valueIndex; // Replace lastValue's index to valueIndex
            }

            // Delete the slot where the moved value was stored
            set._values.pop();

            // Delete the index for the deleted slot
            delete set._indexes[value];

            return true;
        } else {
            return false;
        }
    }

    /**
     * @dev Returns true if the value is in the set. O(1).
     */
    function _contains(Set storage set, bytes32 value) private view returns (bool) {
        return set._indexes[value] != 0;
    }

    /**
     * @dev Returns the number of values on the set. O(1).
     */
    function _length(Set storage set) private view returns (uint256) {
        return set._values.length;
    }

    /**
     * @dev Returns the value stored at position `index` in the set. O(1).
     *
     * Note that there are no guarantees on the ordering of values inside the
     * array, and it may change when more values are added or removed.
     *
     * Requirements:
     *
     * - `index` must be strictly less than {length}.
     */
    function _at(Set storage set, uint256 index) private view returns (bytes32) {
        return set._values[index];
    }

    /**
     * @dev Return the entire set in an array
     *
     * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
     * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
     * this function has an unbounded cost, and using it as part of a state-changing function may render the function
     * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
     */
    function _values(Set storage set) private view returns (bytes32[] memory) {
        return set._values;
    }

    // Bytes32Set

    struct Bytes32Set {
        Set _inner;
    }

    /**
     * @dev Add a value to a set. O(1).
     *
     * Returns true if the value was added to the set, that is if it was not
     * already present.
     */
    function add(Bytes32Set storage set, bytes32 value) internal returns (bool) {
        return _add(set._inner, value);
    }

    /**
     * @dev Removes a value from a set. O(1).
     *
     * Returns true if the value was removed from the set, that is if it was
     * present.
     */
    function remove(Bytes32Set storage set, bytes32 value) internal returns (bool) {
        return _remove(set._inner, value);
    }

    /**
     * @dev Returns true if the value is in the set. O(1).
     */
    function contains(Bytes32Set storage set, bytes32 value) internal view returns (bool) {
        return _contains(set._inner, value);
    }

    /**
     * @dev Returns the number of values in the set. O(1).
     */
    function length(Bytes32Set storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

    /**
     * @dev Returns the value stored at position `index` in the set. O(1).
     *
     * Note that there are no guarantees on the ordering of values inside the
     * array, and it may change when more values are added or removed.
     *
     * Requirements:
     *
     * - `index` must be strictly less than {length}.
     */
    function at(Bytes32Set storage set, uint256 index) internal view returns (bytes32) {
        return _at(set._inner, index);
    }

    /**
     * @dev Return the entire set in an array
     *
     * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
     * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
     * this function has an unbounded cost, and using it as part of a state-changing function may render the function
     * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
     */
    function values(Bytes32Set storage set) internal view returns (bytes32[] memory) {
        bytes32[] memory store = _values(set._inner);
        bytes32[] memory result;

        /// @solidity memory-safe-assembly
        assembly {
            result := store
        }

        return result;
    }

    // AddressSet

    struct AddressSet {
        Set _inner;
    }

    /**
     * @dev Add a value to a set. O(1).
     *
     * Returns true if the value was added to the set, that is if it was not
     * already present.
     */
    function add(AddressSet storage set, address value) internal returns (bool) {
        return _add(set._inner, bytes32(uint256(uint160(value))));
    }

    /**
     * @dev Removes a value from a set. O(1).
     *
     * Returns true if the value was removed from the set, that is if it was
     * present.
     */
    function remove(AddressSet storage set, address value) internal returns (bool) {
        return _remove(set._inner, bytes32(uint256(uint160(value))));
    }

    /**
     * @dev Returns true if the value is in the set. O(1).
     */
    function contains(AddressSet storage set, address value) internal view returns (bool) {
        return _contains(set._inner, bytes32(uint256(uint160(value))));
    }

    /**
     * @dev Returns the number of values in the set. O(1).
     */
    function length(AddressSet storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

    /**
     * @dev Returns the value stored at position `index` in the set. O(1).
     *
     * Note that there are no guarantees on the ordering of values inside the
     * array, and it may change when more values are added or removed.
     *
     * Requirements:
     *
     * - `index` must be strictly less than {length}.
     */
    function at(AddressSet storage set, uint256 index) internal view returns (address) {
        return address(uint160(uint256(_at(set._inner, index))));
    }

    /**
     * @dev Return the entire set in an array
     *
     * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
     * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
     * this function has an unbounded cost, and using it as part of a state-changing function may render the function
     * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
     */
    function values(AddressSet storage set) internal view returns (address[] memory) {
        bytes32[] memory store = _values(set._inner);
        address[] memory result;

        /// @solidity memory-safe-assembly
        assembly {
            result := store
        }

        return result;
    }

    // UintSet

    struct UintSet {
        Set _inner;
    }

    /**
     * @dev Add a value to a set. O(1).
     *
     * Returns true if the value was added to the set, that is if it was not
     * already present.
     */
    function add(UintSet storage set, uint256 value) internal returns (bool) {
        return _add(set._inner, bytes32(value));
    }

    /**
     * @dev Removes a value from a set. O(1).
     *
     * Returns true if the value was removed from the set, that is if it was
     * present.
     */
    function remove(UintSet storage set, uint256 value) internal returns (bool) {
        return _remove(set._inner, bytes32(value));
    }

    /**
     * @dev Returns true if the value is in the set. O(1).
     */
    function contains(UintSet storage set, uint256 value) internal view returns (bool) {
        return _contains(set._inner, bytes32(value));
    }

    /**
     * @dev Returns the number of values in the set. O(1).
     */
    function length(UintSet storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

    /**
     * @dev Returns the value stored at position `index` in the set. O(1).
     *
     * Note that there are no guarantees on the ordering of values inside the
     * array, and it may change when more values are added or removed.
     *
     * Requirements:
     *
     * - `index` must be strictly less than {length}.
     */
    function at(UintSet storage set, uint256 index) internal view returns (uint256) {
        return uint256(_at(set._inner, index));
    }

    /**
     * @dev Return the entire set in an array
     *
     * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
     * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
     * this function has an unbounded cost, and using it as part of a state-changing function may render the function
     * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
     */
    function values(UintSet storage set) internal view returns (uint256[] memory) {
        bytes32[] memory store = _values(set._inner);
        uint256[] memory result;

        /// @solidity memory-safe-assembly
        assembly {
            result := store
        }

        return result;
    }
}

// node_modules/@openzeppelin/contracts-upgradeable/interfaces/IERC3156FlashBorrowerUpgradeable.sol

// OpenZeppelin Contracts (last updated v4.9.0) (interfaces/IERC3156FlashBorrower.sol)

/**
 * @dev Interface of the ERC3156 FlashBorrower, as defined in
 * https://eips.ethereum.org/EIPS/eip-3156[ERC-3156].
 *
 * _Available since v4.1._
 */
interface IERC3156FlashBorrowerUpgradeable {
    /**
     * @dev Receive a flash loan.
     * @param initiator The initiator of the loan.
     * @param token The loan currency.
     * @param amount The amount of tokens lent.
     * @param fee The additional amount of tokens to repay.
     * @param data Arbitrary data structure, intended to contain user-defined parameters.
     * @return The keccak256 hash of "ERC3156FlashBorrower.onFlashLoan"
     */
    function onFlashLoan(
        address initiator,
        address token,
        uint256 amount,
        uint256 fee,
        bytes calldata data
    ) external returns (bytes32);
}

// node_modules/@openzeppelin/contracts-upgradeable/token/ERC20/IERC20Upgradeable.sol

// OpenZeppelin Contracts (last updated v4.9.0) (token/ERC20/IERC20.sol)

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20Upgradeable {
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

// node_modules/@openzeppelin/contracts-upgradeable/token/ERC20/extensions/IERC20PermitUpgradeable.sol

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
interface IERC20PermitUpgradeable {
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

// node_modules/@openzeppelin/contracts-upgradeable/utils/AddressUpgradeable.sol

// OpenZeppelin Contracts (last updated v4.9.0) (utils/Address.sol)

/**
 * @dev Collection of functions related to the address type
 */
library AddressUpgradeable {
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

// contracts/core/hooks/UseLeverage.sol

contract UseLeverage {
    error InvalidNumberOfLoops();
    error InvalidLoanToValue();
    error InvalidPercentageValue();
    error InvalidTargetValue();
    error InvalidDivisor();
    /**
     * @dev Calculates the leverage ratio based on the provided parameters.
     *
     * @param baseValue The base value for leverage calculation.
     * @param loanToValue The loan-to-value ratio (expressed as a percentage with precision).
     * @param nrLoops The number of loops for the iterative calculation.
     * @return The calculated leverage ratio.
     */
    function _calculateLeverageRatio(
        uint256 baseValue,
        uint256 loanToValue,
        uint8 nrLoops
    ) internal pure returns (uint256) {
        if (nrLoops > MAX_LOOPS) revert InvalidNumberOfLoops();
        if (loanToValue == 0 || loanToValue > PERCENTAGE_PRECISION) revert InvalidLoanToValue();
        uint256 leverage = baseValue;
        uint256 prev = baseValue;
        for (uint8 i = 1; i <= nrLoops; ) {
            uint256 inc = (prev * loanToValue) / PERCENTAGE_PRECISION;
            leverage += inc;
            prev = inc;
            unchecked {
                ++i;
            }
        }
        return leverage;
    }

    /**
     * @dev Calculates the changes in collateral and debt based on a specified percentage to burn.
     * @param percentageToBurn The percentage to burn (expressed as a percentage with precision).
     * @param totalCollateralBaseInEth The total collateral base in ETH.
     * @param totalDebtBaseInEth The total debt base in ETH.
     * @return deltaCollateralInETH The change in collateral in ETH.
     * @return deltaDebtInETH The change in debt in ETH.
     */
    function _calcDeltaPosition(
        uint256 percentageToBurn,
        uint256 totalCollateralBaseInEth,
        uint256 totalDebtBaseInEth
    ) internal pure returns (uint256 deltaCollateralInETH, uint256 deltaDebtInETH) {
        if (percentageToBurn == 0 || percentageToBurn > PERCENTAGE_PRECISION) {
            revert InvalidPercentageValue();
        }
        // Reduce Collateral based on the percentage to Burn
        deltaDebtInETH = (totalDebtBaseInEth * percentageToBurn) / PERCENTAGE_PRECISION;
        // Reduce Debt based on the percentage to Burn
        deltaCollateralInETH = (totalCollateralBaseInEth * percentageToBurn) / PERCENTAGE_PRECISION;
    }

    /**
     * @dev Calculates the amount of debt that needs to be paid to achieve a target loan-to-value ratio.
     * @param targetLoanToValue The target loan-to-value ratio (expressed as a percentage with precision).
     * @param collateral The current collateral amount.
     * @param debt The current debt amount.
     * @return delta The additional debt that needs to be paid.
     */
    function _calculateDebtToPay(
        uint256 targetLoanToValue,
        uint256 collateral,
        uint256 debt
    ) internal pure returns (uint256 delta) {
        uint256 colValue = ((targetLoanToValue * collateral) / PERCENTAGE_PRECISION);
        if (colValue >= debt) revert InvalidTargetValue();
        uint256 numerator = debt - colValue;
        uint256 divisor = (PERCENTAGE_PRECISION - targetLoanToValue);
        if (divisor == 0) revert InvalidDivisor();
        delta = (numerator * PERCENTAGE_PRECISION) / divisor;
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

// contracts/interfaces/uniswap/v2/IUniswapV2Router02.sol

interface IUniswapV2Router02 is IUniswapV2Router01 {
    function removeLiquidityETHSupportingFeeOnTransferTokens(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external returns (uint amountETH);
    function removeLiquidityETHWithPermitSupportingFeeOnTransferTokens(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline,
        bool approveMax,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external returns (uint amountETH);

    function swapExactTokensForTokensSupportingFeeOnTransferTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external;
    function swapExactETHForTokensSupportingFeeOnTransferTokens(
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external payable;
    function swapExactTokensForETHSupportingFeeOnTransferTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external;
}

// node_modules/@openzeppelin/contracts-upgradeable/interfaces/IERC3156FlashLenderUpgradeable.sol

// OpenZeppelin Contracts v4.4.1 (interfaces/IERC3156FlashLender.sol)

/**
 * @dev Interface of the ERC3156 FlashLender, as defined in
 * https://eips.ethereum.org/EIPS/eip-3156[ERC-3156].
 *
 * _Available since v4.1._
 */
interface IERC3156FlashLenderUpgradeable {
    /**
     * @dev The amount of currency available to be lended.
     * @param token The loan currency.
     * @return The amount of `token` that can be borrowed.
     */
    function maxFlashLoan(address token) external view returns (uint256);

    /**
     * @dev The fee to be charged for a given loan.
     * @param token The loan currency.
     * @param amount The amount of tokens lent.
     * @return The amount of `token` to be charged for the loan, on top of the returned principal.
     */
    function flashFee(address token, uint256 amount) external view returns (uint256);

    /**
     * @dev Initiate a flash loan.
     * @param receiver The receiver of the tokens in the loan, and the receiver of the callback.
     * @param token The loan currency.
     * @param amount The amount of tokens lent.
     * @param data Arbitrary data structure, intended to contain user-defined parameters.
     */
    function flashLoan(
        IERC3156FlashBorrowerUpgradeable receiver,
        address token,
        uint256 amount,
        bytes calldata data
    ) external returns (bool);
}

// node_modules/@openzeppelin/contracts-upgradeable/proxy/utils/Initializable.sol

// OpenZeppelin Contracts (last updated v4.9.0) (proxy/utils/Initializable.sol)


abstract contract Initializable {
    /**
     * @dev Indicates that the contract has been initialized.
     * @custom:oz-retyped-from bool
     */
    uint8 private _initialized;

    /**
     * @dev Indicates that the contract is in the process of being initialized.
     */
    bool private _initializing;

    /**
     * @dev Triggered when the contract has been initialized or reinitialized.
     */
    event Initialized(uint8 version);

    /**
     * @dev A modifier that defines a protected initializer function that can be invoked at most once. In its scope,
     * `onlyInitializing` functions can be used to initialize parent contracts.
     *
     * Similar to `reinitializer(1)`, except that functions marked with `initializer` can be nested in the context of a
     * constructor.
     *
     * Emits an {Initialized} event.
     */
    modifier initializer() {
        bool isTopLevelCall = !_initializing;
        require(
            (isTopLevelCall && _initialized < 1) || (!AddressUpgradeable.isContract(address(this)) && _initialized == 1),
            "Initializable: contract is already initialized"
        );
        _initialized = 1;
        if (isTopLevelCall) {
            _initializing = true;
        }
        _;
        if (isTopLevelCall) {
            _initializing = false;
            emit Initialized(1);
        }
    }

    /**
     * @dev A modifier that defines a protected reinitializer function that can be invoked at most once, and only if the
     * contract hasn't been initialized to a greater version before. In its scope, `onlyInitializing` functions can be
     * used to initialize parent contracts.
     *
     * A reinitializer may be used after the original initialization step. This is essential to configure modules that
     * are added through upgrades and that require initialization.
     *
     * When `version` is 1, this modifier is similar to `initializer`, except that functions marked with `reinitializer`
     * cannot be nested. If one is invoked in the context of another, execution will revert.
     *
     * Note that versions can jump in increments greater than 1; this implies that if multiple reinitializers coexist in
     * a contract, executing them in the right order is up to the developer or operator.
     *
     * WARNING: setting the version to 255 will prevent any future reinitialization.
     *
     * Emits an {Initialized} event.
     */
    modifier reinitializer(uint8 version) {
        require(!_initializing && _initialized < version, "Initializable: contract is already initialized");
        _initialized = version;
        _initializing = true;
        _;
        _initializing = false;
        emit Initialized(version);
    }

    /**
     * @dev Modifier to protect an initialization function so that it can only be invoked by functions with the
     * {initializer} and {reinitializer} modifiers, directly or indirectly.
     */
    modifier onlyInitializing() {
        require(_initializing, "Initializable: contract is not initializing");
        _;
    }

    /**
     * @dev Locks the contract, preventing any future reinitialization. This cannot be part of an initializer call.
     * Calling this in the constructor of a contract will prevent that contract from being initialized or reinitialized
     * to any version. It is recommended to use this to lock implementation contracts that are designed to be called
     * through proxies.
     *
     * Emits an {Initialized} event the first time it is successfully executed.
     */
    function _disableInitializers() internal virtual {
        require(!_initializing, "Initializable: contract is initializing");
        if (_initialized != type(uint8).max) {
            _initialized = type(uint8).max;
            emit Initialized(type(uint8).max);
        }
    }

    /**
     * @dev Returns the highest version that has been initialized. See {reinitializer}.
     */
    function _getInitializedVersion() internal view returns (uint8) {
        return _initialized;
    }

    /**
     * @dev Returns `true` if the contract is currently initializing. See {onlyInitializing}.
     */
    function _isInitializing() internal view returns (bool) {
        return _initializing;
    }
}

// contracts/interfaces/core/IStrategyLeverage.sol

/**
 * @title IStrategyLeverage
 *
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 * @author Chef Kal-EL <chef.kal-el@bakerfi.xyz>
 *
 * @notice Interface used for Leverage Strategy
 */
interface IStrategyLeverage is IStrategy {
    /**
     * @dev Return the Address of the Asset used as Collatteral
     */
    function getCollateralAsset() external view returns (address);
    /**
     * @dev Return the Address of the Debt Asset used as Debt
     */
    function getDebAsset() external view returns (address);

    /**
     * @dev Return the Collatetal/Debt/Loan Balances in USD and Loan To Value
     *
     * @param priceOptions The Oracle optios
     */
    function getPosition(
        IOracle.PriceOptions memory priceOptions
    ) external view returns (uint256 totalCollateralInUSD, uint256 totalDebtInUSD, uint256 loanToValue);
}

// node_modules/@openzeppelin/contracts-upgradeable/security/ReentrancyGuardUpgradeable.sol

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
abstract contract ReentrancyGuardUpgradeable is Initializable {
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

    function __ReentrancyGuard_init() internal onlyInitializing {
        __ReentrancyGuard_init_unchained();
    }

    function __ReentrancyGuard_init_unchained() internal onlyInitializing {
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

    /**
     * @dev This empty reserved space is put in place to allow future versions to add new
     * variables without shifting down storage in the inheritance chain.
     * See https://docs.openzeppelin.com/contracts/4.x/upgradeable#storage_gaps
     */
    uint256[49] private __gap;
}

// node_modules/@openzeppelin/contracts-upgradeable/utils/ContextUpgradeable.sol

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
abstract contract ContextUpgradeable is Initializable {
    function __Context_init() internal onlyInitializing {
    }

    function __Context_init_unchained() internal onlyInitializing {
    }
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }

    function _contextSuffixLength() internal view virtual returns (uint256) {
        return 0;
    }

    /**
     * @dev This empty reserved space is put in place to allow future versions to add new
     * variables without shifting down storage in the inheritance chain.
     * See https://docs.openzeppelin.com/contracts/4.x/upgradeable#storage_gaps
     */
    uint256[50] private __gap;
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

// node_modules/@openzeppelin/contracts-upgradeable/access/OwnableUpgradeable.sol

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
abstract contract OwnableUpgradeable is Initializable, ContextUpgradeable {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    function __Ownable_init() internal onlyInitializing {
        __Ownable_init_unchained();
    }

    function __Ownable_init_unchained() internal onlyInitializing {
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

    /**
     * @dev This empty reserved space is put in place to allow future versions to add new
     * variables without shifting down storage in the inheritance chain.
     * See https://docs.openzeppelin.com/contracts/4.x/upgradeable#storage_gaps
     */
    uint256[49] private __gap;
}

// node_modules/@openzeppelin/contracts-upgradeable/token/ERC20/utils/SafeERC20Upgradeable.sol

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
library SafeERC20Upgradeable {
    using AddressUpgradeable for address;

    /**
     * @dev Transfer `value` amount of `token` from the calling contract to `to`. If `token` returns no value,
     * non-reverting calls are assumed to be successful.
     */
    function safeTransfer(IERC20Upgradeable token, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    /**
     * @dev Transfer `value` amount of `token` from `from` to `to`, spending the approval given by `from` to the
     * calling contract. If `token` returns no value, non-reverting calls are assumed to be successful.
     */
    function safeTransferFrom(IERC20Upgradeable token, address from, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(IERC20Upgradeable token, address spender, uint256 value) internal {
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
    function safeIncreaseAllowance(IERC20Upgradeable token, address spender, uint256 value) internal {
        uint256 oldAllowance = token.allowance(address(this), spender);
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, oldAllowance + value));
    }

    /**
     * @dev Decrease the calling contract's allowance toward `spender` by `value`. If `token` returns no value,
     * non-reverting calls are assumed to be successful.
     */
    function safeDecreaseAllowance(IERC20Upgradeable token, address spender, uint256 value) internal {
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
    function forceApprove(IERC20Upgradeable token, address spender, uint256 value) internal {
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
        IERC20PermitUpgradeable token,
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
    function _callOptionalReturn(IERC20Upgradeable token, bytes memory data) private {
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
    function _callOptionalReturnBool(IERC20Upgradeable token, bytes memory data) private returns (bool) {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We cannot use {Address-functionCall} here since this should return false
        // and not revert is the subcall reverts.

        (bool success, bytes memory returndata) = address(token).call(data);
        return
            success && (returndata.length == 0 || abi.decode(returndata, (bool))) && AddressUpgradeable.isContract(address(token));
    }
}

// contracts/core/GovernableOwnable.sol

/**
 * @title An Upgradable GovernableOwnable Contract
 *
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 * @author Chef Kal-EL <chef.kal-el@bakerfi.xyz>
 *
 * @dev A Contract that could have an independent owner and governor
 *
 * This is quite usesufull when you dont need to have more than 2 roles on a contract
 *
 */
contract GovernableOwnable is OwnableUpgradeable {
    address private _governor;

    error CallerNotTheGovernor();
    error InvalidGovernorAddress();

    event GovernshipTransferred(address indexed previousGovernor, address indexed newGovernor);

    function _initializeGovernableOwnable(address initialOwner, address initialGovernor) internal initializer {
        _transferOwnership(initialOwner);
        _transferGovernorship(initialGovernor);
    }

    /**
     * Modifier that checks if the caller is governor
     */
    modifier onlyGovernor() {
        if (msg.sender != governor()) revert CallerNotTheGovernor();
        _;
    }

    /**
     * Gets the Governor of the contrat
     */
    function governor() public view virtual returns (address) {
        return _governor;
    }

    /**
     * Changes the contract Governor
     * @param _newGovernor the new Governor addres
     */
    function transferGovernorship(address _newGovernor) public virtual onlyGovernor {
        if (_newGovernor == address(0)) revert InvalidGovernorAddress();
        _transferGovernorship(_newGovernor);
    }

    function _transferGovernorship(address newGovernor) internal virtual {
        emit GovernshipTransferred(_governor, newGovernor);
        _governor = newGovernor;
    }
}

// contracts/core/hooks/UseFlashLender.sol

abstract contract UseFlashLender is Initializable {
    IERC3156FlashLenderUpgradeable private _fLender;

    error InvalidFlashLenderContract();

    function _initUseFlashLender(address iflashLender) internal onlyInitializing {
        _fLender = IERC3156FlashLenderUpgradeable(iflashLender);
        if (address(_fLender) == address(0)) revert InvalidFlashLenderContract();
    }

    function flashLender() internal view returns (IERC3156FlashLenderUpgradeable) {
        return _fLender;
    }
    function flashLenderA() internal view returns (address) {
        return address(_fLender);
    }
}

// contracts/libraries/AerodromeLibrary.sol

/**
 * @title AerodromeLibrary
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>

 * @dev Library for handling Aerodrome swaps
 */
library AerodromeLibrary {
    using SafeERC20 for IERC20;
    error InvalidInputToken();
    error InvalidOutputToken();
    error SwapFailed();
    error NotSupported();
    error FailedToApproveAllowance();

    /**
     * @notice Swaps tokens using Uniswap V2
     * @param router The Uniswap V2 Router address
     * @param params The swap parameters
     * @return amountIn The actual input amount
     * @return amountOut The actual output amount
     */
    function swapAerodrome(
        ISwapRouter router,
        ISwapHandler.SwapParams memory params
    ) internal returns (uint256 amountIn, uint256 amountOut) {
        // Validate input token address
        if (params.underlyingIn == address(0)) revert InvalidInputToken();
        // Validate output token address
        if (params.underlyingOut == address(0)) revert InvalidOutputToken();

        int24 tickspacing = abi.decode(params.payload, (int24));

        // Handle Exact Input swaps
        if (params.mode == ISwapHandler.SwapType.EXACT_INPUT) {
            amountIn = params.amountIn; // Set the input amount
            // Execute the swap using the Uniswap V3 router
            amountOut = router.exactInputSingle(
                ISwapRouter.ExactInputSingleParams({
                    tokenIn: params.underlyingIn,
                    tokenOut: params.underlyingOut,
                    amountIn: amountIn,
                    amountOutMinimum: params.amountOut,
                    tickSpacing: tickspacing,
                    recipient: address(this),
                    deadline: block.timestamp,
                    sqrtPriceLimitX96: 0
                })
            );
            // Check if the swap was successful
            if (amountOut == 0) {
                revert SwapFailed(); // Revert if the output amount is zero
            }

            // Handle Exact Output swaps
        } else if (params.mode == ISwapHandler.SwapType.EXACT_OUTPUT) {
            amountOut = params.amountOut; // Set the expected output amount
            // Execute the swap using the Uniswap V3 router
            amountIn = router.exactOutputSingle(
                ISwapRouter.ExactOutputSingleParams({
                    tokenIn: params.underlyingIn,
                    tokenOut: params.underlyingOut,
                    tickSpacing: tickspacing,
                    recipient: address(this),
                    deadline: block.timestamp,
                    amountOut: amountOut,
                    amountInMaximum: params.amountIn,
                    sqrtPriceLimitX96: 0
                })
            );
        }
    }
}

// contracts/libraries/UniV3Library.sol

/**
 * @title UniV3Library
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 * @dev Library for handling Uniswap V3 swaps
 */
library UniV3Library {
    using SafeERC20 for IERC20;

    error InvalidInputToken();
    error InvalidOutputToken();
    error InvalidFeeTier();
    error SwapFailed();

    /**
     * @notice Swaps tokens using Uniswap V3
     * @param router The Uniswap V3 Router address
     * @param params The swap parameters
     * @return amountIn The actual input amount
     * @return amountOut The actual output amount
     */
    function swapUniV3(
        IV3SwapRouter router,
        ISwapHandler.SwapParams memory params
    ) internal returns (uint256 amountIn, uint256 amountOut) {
        // Validate input token address
        if (params.underlyingIn == address(0)) revert InvalidInputToken();
        // Validate output token address
        if (params.underlyingOut == address(0)) revert InvalidOutputToken();
        // Validate fee tier
        uint24 fee = abi.decode(params.payload, (uint24));
        if (fee == 0) revert InvalidFeeTier();

        // Handle Exact Input swaps
        if (params.mode == ISwapHandler.SwapType.EXACT_INPUT) {
            amountIn = params.amountIn; // Set the input amount
            // Execute the swap using the Uniswap V3 router
            amountOut = router.exactInputSingle(
                IV3SwapRouter.ExactInputSingleParams({
                    tokenIn: params.underlyingIn,
                    tokenOut: params.underlyingOut,
                    amountIn: amountIn,
                    amountOutMinimum: params.amountOut,
                    fee: fee,
                    recipient: address(this),
                    sqrtPriceLimitX96: 0
                })
            );
            // Check if the swap was successful
            if (amountOut == 0) {
                revert SwapFailed(); // Revert if the output amount is zero
            }

            // Handle Exact Output swaps
        } else if (params.mode == ISwapHandler.SwapType.EXACT_OUTPUT) {
            amountOut = params.amountOut; // Set the expected output amount
            // Execute the swap using the Uniswap V3 router
            amountIn = router.exactOutputSingle(
                IV3SwapRouter.ExactOutputSingleParams({
                    tokenIn: params.underlyingIn,
                    tokenOut: params.underlyingOut,
                    fee: fee,
                    recipient: address(this),
                    amountOut: amountOut,
                    amountInMaximum: params.amountIn,
                    sqrtPriceLimitX96: 0
                })
            );
        }
    }
}

// contracts/libraries/UniV2Library.sol

/**
 * @title UniV2Library
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 * @dev Library for handling Uniswap V2 swaps
 */
library UniV2Library {
    using SafeERC20 for IERC20;
    error InvalidInputToken();
    error InvalidOutputToken();
    error SwapFailed();
    error FailedToApproveAllowance();

    /**
     * @notice Swaps tokens using Uniswap V2
     * @param router The Uniswap V2 Router address
     * @param params The swap parameters
     * @return amountIn The actual input amount
     * @return amountOut The actual output amount
     */
    function swapUniV2(
        IUniswapV2Router02 router,
        ISwapHandler.SwapParams memory params
    ) internal returns (uint256 amountIn, uint256 amountOut) {
        // Check if the input token address is valid
        if (params.underlyingIn == address(0)) revert InvalidInputToken();
        // Check if the output token address is valid
        if (params.underlyingOut == address(0)) revert InvalidOutputToken();

        // Create an array to hold the path for the Uniswap V2 swap
        address[] memory path = new address[](2);
        path[0] = params.underlyingIn; // Set the first element of the path to the input token
        path[1] = params.underlyingOut; // Set the second element of the path to the output token

        // Handle the case for Exact Input swaps
        if (params.mode == ISwapHandler.SwapType.EXACT_INPUT) {
            // Allow the Uniswap router to spend the specified amount of the input token
            if (!IERC20(params.underlyingIn).approve(address(router), params.amountIn))
                revert FailedToApproveAllowance();

            // Determine the minimum amount of output tokens to receive
            uint256 amountOutMin = 0;
            if (params.amountOut > 0) {
                amountOutMin = params.amountOut; // Use the specified minimum amount if provided
            } else {
                // Calculate the expected output amount based on the input amount
                uint256[] memory amountsOut = router.getAmountsOut(params.amountIn, path);
                amountOutMin = amountsOut[amountsOut.length - 1]; // Get the last amount in the array as the minimum output
            }

            // Execute the swap on Uniswap V2
            amountIn = params.amountIn; // Set the amountIn to the input amount
            uint256[] memory amounts = router.swapExactTokensForTokens(
                amountIn,
                amountOutMin,
                path,
                address(this), // Send the output tokens to this contract
                block.timestamp // Set the deadline for the swap to the current block timestamp
            );
            amountOut = amounts[amounts.length - 1]; // Get the actual output amount from the swap

            // Handle the case for Exact Output swaps
        } else if (params.mode == ISwapHandler.SwapType.EXACT_OUTPUT) {
            amountOut = params.amountOut; // Set the expected output amount
            uint256 amountInMax = 0; // Initialize the maximum input amount

            // If no input amount is specified, calculate the required input amount for the desired output
            if (params.amountIn == 0) {
                uint256[] memory amountsIn = router.getAmountsIn(amountOut, path);
                amountInMax = amountsIn[0]; // Get the required input amount from the calculation
            } else {
                amountInMax = params.amountIn; // Use the specified maximum input amount
            }

            // Allow the Uniswap router to spend the maximum input amount
            if (!IERC20(params.underlyingIn).approve(address(router), amountInMax)) revert FailedToApproveAllowance();

            // Execute the swap on Uniswap V2 for exact output
            uint256[] memory amounts = router.swapTokensForExactTokens(
                amountOut,
                amountInMax,
                path,
                address(this), // Send the output tokens to this contract
                block.timestamp // Set the deadline for the swap to the current block timestamp
            );
            amountIn = amounts[0]; // Get the actual input amount used in the swap
        }

        // If the output amount is zero, the swap has failed
        if (amountOut == 0) {
            revert SwapFailed(); // Revert the transaction with a failure error
        }
    }
}

// contracts/core/strategies/StrategySettings.sol

/**
 * @title BakerFI Settings(⚙️) Contract
 *
 * @notice The settings could only be changed by the Owner and could be used by any contract by the system.
 *
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 * @author Chef Kal-EL <chef.kal-el@bakerfi.xyz>
 *
 * @dev The `Settings` contract is used to manage protocol settings.
 * It extends the `OwnableUpgradeable` contract and implements the `ISettings` interface.
 * The settings can only be changed by the owner and can be utilized by any contract within the system.
 *
 * This contract is going to be used by any service on the Bakerfi system to retrieve
 * the fees, basic configuration parameters and the list of whitelisted adresess that can
 * interact with the system
 */
abstract contract StrategySettings is GovernableOwnable, IStrategySettings {
    error InvalidOwner();
    error InvalidValue();
    error InvalidPercentage();
    error InvalidAddress();

    using EnumerableSet for EnumerableSet.AddressSet;

    /// @dev Storage slot for price max age
    bytes32 private constant PRICE_MAX_AGE_SLOT = keccak256("bakerfi.strategy.price.max.age");

    /// @dev Storage slot for price max confidence
    bytes32 private constant PRICE_MAX_CONF_SLOT = keccak256("bakerfi.strategy.price.max.conf");

    /// @custom:oz-upgrades-unsafe-allow constructor
    constructor() {
        _disableInitializers();
    }

    /**
     * @dev Initializes the contract.
     *
     * This function is used for the initial setup of the contract, setting the owner, withdrawal fee,
     * performance fee, fee receiver, loan-to-value ratio, maximum loan-to-value ratio, and the number of loops.
     *
     * Requirements:
     * - The provided owner address must not be the zero address.
     */
    function _initializeStrategySettings() internal onlyInitializing {
        _setUint256(PRICE_MAX_AGE_SLOT, 60 minutes);
        _setUint256(PRICE_MAX_CONF_SLOT, 0);
    }

    /**
     * Sets the max age for price retrievals
     * @notice Sets the maximum age of the price data.
     *
     * @dev Setting the maxAge to 0 is quite dangerous and the protocol could be working
     * with stale prices
     * @param value The maximum age in seconds.
     */
    function setPriceMaxAge(uint256 value) external onlyGovernor {
        _setUint256(PRICE_MAX_AGE_SLOT, value);
        emit PriceMaxAgeChanged(value);
    }

    /**
     * @notice Retrieves the maximum age of the price data.
     * @return The maximum age in seconds.
     */
    function getPriceMaxAge() public view returns (uint256) {
        return _getUint256(PRICE_MAX_AGE_SLOT);
    }

    /**
     * @notice Sets the maximum confidence level for the price data in percentage
     * @param value The maximum confidence level.
     */
    function setPriceMaxConf(uint256 value) external onlyGovernor {
        if (value > PERCENTAGE_PRECISION) revert InvalidPercentage();
        _setUint256(PRICE_MAX_CONF_SLOT, value);
        emit PriceMaxConfChanged(value);
    }

    /**
     * @notice Retrieves the maximum confidence level for the price data.
     * @return The maximum confidence level.
     */
    function getPriceMaxConf() public view returns (uint256) {
        return _getUint256(PRICE_MAX_CONF_SLOT);
    }

    // Add helper functions for storage slots
    function _setUint256(bytes32 slot, uint256 value) private {
        assembly {
            sstore(slot, value)
        }
    }

    function _getUint256(bytes32 slot) private view returns (uint256 value) {
        assembly {
            value := sload(slot)
        }
    }
}

// contracts/core/strategies/StrategyLeverageSettings.sol

contract StrategyLeverageSettings is StrategySettings {
    error InvalidMaxLoanToValue();
    error InvalidLoopCount();

    /**
     * @dev Emitted when the maximum allowed loan-to-value ratio is changed.
     *
     * This event provides information about the updated maximum loan-to-value ratio.
     *
     * @param value The new maximum allowed loan-to-value ratio.
     */
    event MaxLoanToValueChanged(uint256 indexed value);

    /**
     * @dev Emitted when the general loan-to-value ratio is changed.
     *
     * This event provides information about the updated loan-to-value ratio.
     *
     * @param value The new general loan-to-value ratio.
     */
    event LoanToValueChanged(uint256 indexed value);

    /**
     * @dev Emitted when the number of loops for a specific process is changed.
     *
     * This event provides information about the updated number of loops.
     *
     * @param value The new number of loops.
     */
    event NrLoopsChanged(uint256 indexed value);

    event MaxSlippageChanged(uint256 indexed value);

    /**
     * @dev The loan-to-value ratio for managing loans.
     *
     * This private state variable holds the loan-to-value ratio, represented as an integer.
     */
    uint256 private _loanToValue; // 80%

    /**
     * @dev The maximum allowed loan-to-value ratio.
     *
     * This private state variable holds the maximum allowed loan-to-value ratio, represented as an integer.
     */
    uint256 private _maxLoanToValue; // 85%

    /**
     * @dev The number of loops for a specific process.
     *
     * This private state variable holds the number of loops for a specific process, represented as an unsigned integer.
     */
    uint8 private _nrLoops;

    /**
     * @dev
     */
    uint256 private _maxSlippage;

    function _initLeverageSettings(address initialOwner, address initialGovernor) internal initializer {
        _initializeGovernableOwnable(initialOwner, initialGovernor);
        _initializeStrategySettings();
        _loanToValue = 800 * 1e6; // 80%
        _maxLoanToValue = 850 * 1e6; // 85%
        _nrLoops = 10;
        _maxSlippage = 0; // By Default there is no slippage protection
    }

    /**
     * @dev Sets the maximum allowed loan-to-value ratio.
     *
     * This function can only be called by the owner and is used to update the maximum allowed loan-to-value ratio.
     * Emits a {MaxLoanToValueChanged} event upon successful update.
     *
     * @param maxLoanToValue The new maximum allowed loan-to-value ratio to be set.
     *
     * Requirements:
     * - The caller must be the owner of the contract.
     */
    function setMaxLoanToValue(uint256 maxLoanToValue) external onlyGovernor {
        if (maxLoanToValue == 0) revert InvalidValue();
        if (maxLoanToValue > PERCENTAGE_PRECISION) revert InvalidPercentage();
        if (maxLoanToValue < _loanToValue) revert InvalidMaxLoanToValue();
        _maxLoanToValue = maxLoanToValue;
        emit MaxLoanToValueChanged(_maxLoanToValue);
    }
    /**
     * @dev Retrieves the maximum allowed loan-to-value ratio.
     *
     * This function is externally callable and returns the maximum allowed loan-to-value ratio.
     *
     * @return maxLoanToValue The maximum allowed loan-to-value ratio.
     */
    function getMaxLoanToValue() public view returns (uint256) {
        return _maxLoanToValue;
    }

    /**
     * @dev Sets the general loan-to-value ratio.
     *
     * This function can only be called by the owner and is used to update the general loan-to-value ratio.
     * Emits a {LoanToValueChanged} event upon successful update.
     *
     * @param loanToValue The new general loan-to-value ratio to be set.
     *
     * Requirements:
     * - The caller must be the owner of the contract.
     * - The new loan-to-value ratio must be less than or equal to the maximum allowed loan-to-value ratio.
     * - The new loan-to-value ratio must be a valid percentage value.
     * - The new loan-to-value ratio must be greater than 0.
     */
    function setLoanToValue(uint256 loanToValue) external onlyGovernor {
        if (loanToValue > _maxLoanToValue) revert InvalidValue();
        if (loanToValue > PERCENTAGE_PRECISION) revert InvalidPercentage();
        if (loanToValue == 0) revert InvalidValue();
        _loanToValue = loanToValue;
        emit LoanToValueChanged(_loanToValue);
    }

    /**
     * @dev Retrieves the general loan-to-value ratio.
     *
     * This function is externally callable and returns the general loan-to-value ratio.
     *
     * @return loanToValue The general loan-to-value ratio.
     */
    function getLoanToValue() public view returns (uint256) {
        return _loanToValue;
    }

    /**
     * @dev Retrieves the number of loops for our Recursive Staking Strategy
     *
     * This function is externally callable and returns the number of loops configured.
     *
     * @return nrLoops The number of loops.
     */
    function getNrLoops() public view returns (uint8) {
        return _nrLoops;
    }

    /**
     * @dev Sets the number of loops for our Recursive Staking Strategy
     *
     * This function can only be called by the owner and is used to update the number of loops.
     * Emits an {NrLoopsChanged} event upon successful update.
     *
     * @param nrLoops The new number of loops to be set.
     *
     * Requirements:
     * - The caller must be the owner of the contract.
     * - The new number of loops must be less than the maximum allowed number of loops.
     */
    function setNrLoops(uint8 nrLoops) external onlyGovernor {
        if (nrLoops > MAX_LOOPS) revert InvalidLoopCount();
        _nrLoops = nrLoops;
        emit NrLoopsChanged(_nrLoops);
    }

    function getMaxSlippage() public view returns (uint256) {
        return _maxSlippage;
    }

    function setMaxSlippage(uint256 slippage) external onlyGovernor {
        if (slippage > PERCENTAGE_PRECISION) revert InvalidPercentage();
        _maxSlippage = slippage;
        emit MaxSlippageChanged(slippage);
    }

    /**
     * @dev This empty reserved space is put in place to allow future versions to add new
     * settings without shifting down storage in the inheritance chain.
     */
    uint256[25] private __gap;
}

// contracts/core/hooks/swappers/UseUnifiedSwapper.sol

/**
 * @title UseUnifiedSwapper
 *
 * @notice A contract that allows to swap tokens using different implementations of the swapper
 *
 * Supports Uniswap V3, Uniswap V2, and Aerodrome
 *
 * Manages authorized routes for swaps acting as a unified swap router for different swap implementations.
 * Integrating multiple DEX protocols (Uniswap V2, V3, and Aerodrome)
 *
 * It prevens memory layout collisions on upgrades
 *
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 * @author Chef Kal-El <chef.kal-el@bakerfi.xyz>
 */
abstract contract UseUnifiedSwapper is ISwapHandler, GovernableOwnable {
    using SafeERC20 for IERC20;
    error InvalidRouter();
    error RouteAlreadyAuthorized();
    error RouteNotAuthorized();
    error FailedToApproveAllowance();
    error InvalidProvider();
    /**
     * @notice The provider of the swap
     */
    enum SwapProvider {
        NONE,
        UNIV3,
        UNIV2,
        AERODROME
    }
    /**
     * @notice The information about a route
     */
    struct RouteInfo {
        SwapProvider provider; // 1byte one, UniswapV3, UniswapV2, Aerodrome
        address router; // Protocol Router
        uint24 uniV3Tier; // 3 bytes UniswapV3 fee tier
        uint24 tickSpacing; // 3 bytes tick spacing
    }

    mapping(bytes32 => RouteInfo) private _routes;

    function _key(address tokenA, address tokenB) internal pure returns (bytes32) {
        return keccak256(abi.encode(tokenA < tokenB ? [tokenA, tokenB] : [tokenB, tokenA]));
    }
    /**
     * @notice Enables a route for a given pair of tokens
     * @param tokenIn The input token address
     * @param tokenOut The output token address
     * @param routeInfo The route information
     */
    function enableRoute(address tokenIn, address tokenOut, RouteInfo memory routeInfo) external onlyGovernor {
        bytes32 key = _key(tokenIn, tokenOut);
        // Check if the route is already authorized
        if (_routes[key].provider != SwapProvider.NONE) revert RouteAlreadyAuthorized();
        // Set the route information
        if (!IERC20(tokenIn).approve(routeInfo.router, type(uint256).max - 1)) revert FailedToApproveAllowance();

        if (!IERC20(tokenOut).approve(routeInfo.router, type(uint256).max - 1)) revert FailedToApproveAllowance();

        _routes[key] = routeInfo;
    }

    /**
     * @notice Disables a route for a given pair of tokens
     * @param tokenIn The input token address
     * @param tokenOut The output token address
     */
    function disableRoute(address tokenIn, address tokenOut) external onlyGovernor {
        // Check if the route is authorized
        bytes32 key = _key(tokenIn, tokenOut);
        // Check if the route is authorized
        if (_routes[key].provider == SwapProvider.NONE) revert RouteNotAuthorized();
        // Set the allowance to 0
        if (!IERC20(tokenIn).approve(_routes[key].router, 0)) revert FailedToApproveAllowance();
        if (!IERC20(tokenOut).approve(_routes[key].router, 0)) revert FailedToApproveAllowance();
        // Set the route information to none
        _routes[key].provider = SwapProvider.NONE;
    }

    /**
     * @notice Checks if a route is authorized for a given pair of tokens
     * @param tokenIn The input token address
     * @param tokenOut The output token address
     * @return true if the route is authorized, false otherwise
     */
    function isRouteEnabled(address tokenIn, address tokenOut) public view returns (bool) {
        bytes32 key = _key(tokenIn, tokenOut);
        return _routes[key].provider != SwapProvider.NONE;
    }

    /**
    * @inheritdoc ISwapHandler
    * @notice The swap function is responsible for executing token swaps based on the authorized routes.
    * It retrieves the route information, checks if the route is authorized, and then determines
    * the appropriate swap pro
    -+
    vider to execute the swap. The function handles swaps for Uniswap V2,
    * Uniswap V3, and Curve, encoding the necessary parameters for the Curve swap.
   */
    function swap(SwapParams memory params) internal virtual override returns (uint256 amountIn, uint256 amountOut) {
        bytes32 key = _key(params.underlyingIn, params.underlyingOut);
        // Retrieve the route information using the storage getter
        RouteInfo memory routeInfo = _routes[key];
        // Check if the route is authorized; if not, revert the transaction with an error
        if (routeInfo.provider == SwapProvider.NONE) revert RouteNotAuthorized();
        // Determine the swap provider based on the route information
        if (routeInfo.provider == SwapProvider.UNIV3) {
            // If the provider is Uniswap V3, set the fee tier for the swap parameters
            params.payload = abi.encode(routeInfo.uniV3Tier);
            // Execute the swap using the Uniswap V3 swapper and return the result
            return UniV3Library.swapUniV3(IV3SwapRouter(routeInfo.router), params);
        } else if (routeInfo.provider == SwapProvider.UNIV2) {
            // If the provider is Uniswap V2, execute the swap using the Uniswap V2 swapper and return the result
            return UniV2Library.swapUniV2(IUniswapV2Router02(routeInfo.router), params);
        } else if (routeInfo.provider == SwapProvider.AERODROME) {
            params.payload = abi.encode(routeInfo.tickSpacing);
            return AerodromeLibrary.swapAerodrome(ISwapRouter(routeInfo.router), params);
        } else {
            revert InvalidProvider();
        }
    }
}
/**
 * @title UseUnifiedSwapperMock
 * @notice A mock contract for testing the UseUnifiedSwapper contract
 */
contract UseUnifiedSwapperMock is UseUnifiedSwapper {
    constructor() {
        _transferOwnership(msg.sender);
        _transferGovernorship(msg.sender);
    }
    /**
     * @notice Tests the swap function
     * @param params The swap parameters
     * @return amountIn The amount of input tokens used in the swap
     * @return amountOut The amount of output tokens received from the swap
     */
    function test__swap(SwapParams memory params) external returns (uint256 amountIn, uint256 amountOut) {
        return UseUnifiedSwapper.swap(params);
    }
}

// contracts/core/strategies/StrategyLeverage.sol

/**
 * @title Base Recursive Staking Strategy
 *
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 * @author Chef Kal-EL <chef.kal-el@bakerfi.xyz>
 *
 * @dev This contract implements a strategy and could be used to deploy a ERC-20 on a AAVE with
 * the a recursive staking strategy and receive an amplified yield
 *
 * The Strategy interacts with :
 *
 * ✅ BalancerFlashLender to request a flash loan from Balancer
 * ✅ Uniswap to convert from collateral token to debt token
 * ✅ Uniswap Quoter to request a precise price token
 * ✅ AAVE as the lending/borrow market
 *
 * The APY of this strategy depends on the followwin factors:
 *
 *  ✅ Lido APY
 *  ✅ AAVE v3 Borrow Rate
 *  ✅ Target Loan to Value
 *  ✅ Number of Loops on the recursive Strategy
 *
 *  Flow Deposit:
 *  1) Deploy X amount of ETH/ERC20
 *  2) Borrow Y Amount of ETH/ERC20
 *  3) Deposit X+Y amount of Collateral in AAVE
 *  4) Borrow Y ETH/ERC20 From AAVE to pay the flash loan
 *  5) Ends up with X+Y Amount of Collateral and Y of Debt
 *
 *  This strategy could work for
 *  rETH/WETH
 *  wstETH/WETH
 *  sUSD/DAI
 *
 *  ...
 *
 * @notice The Contract is abstract and needs to be extended to implement the
 * conversion between debt token and the collateral , to integrate a money market
 */
abstract contract StrategyLeverage is
    IStrategyLeverage,
    IERC3156FlashBorrowerUpgradeable,
    StrategyLeverageSettings,
    ReentrancyGuardUpgradeable,
    UseUnifiedSwapper,
    UseFlashLender,
    EmptySlot,
    UseLeverage
{
    enum FlashLoanAction {
        SUPPLY_BORROW,
        PAY_DEBT_WITHDRAW,
        PAY_DEBT
    }

    struct FlashLoanData {
        uint256 originalAmount;
        address receiver;
        FlashLoanAction action;
    }

    bytes32 private constant _SUCCESS_MESSAGE = keccak256("ERC3156FlashBorrower.onFlashLoan");

    using SafeERC20Upgradeable for IERC20Upgradeable;
    using AddressUpgradeable for address;
    using AddressUpgradeable for address payable;
    using MathLibrary for uint256;

    error InvalidDebtToken();
    error InvalidCollateralToken();
    error InvalidOracle();
    error InvalidDeployAmount();
    error InvalidAllowance();
    error FailedToRunFlashLoan();
    error InvalidFlashLoanSender();
    error InvalidLoanInitiator();
    error InvalidFlashLoanAsset();
    error CollateralLowerThanDebt();
    error InvalidDeltaDebt();
    error PriceOutdated();
    error NoCollateralMarginToScale();
    error ETHTransferNotAllowed(address sender);
    error FailedToAuthenticateArgs();
    error InvalidFlashLoanAction();

    // Assets in debtToken() Controlled by the strategy that can be unwinded
    uint256 private _deployedAssets = 0;
    // Collateral IERC20 Token used on this leverage Position
    address internal _collateralToken;
    // Debt IERC20 Token address used on this
    address internal _debtToken;
    // Oracle used to get the price of the collateral and debt
    IOracle private _oracle;
    // Two Empty Slots to keep the storage layout consistent
    uint256[1] internal _emptySlots;
    // Internal Storaged used for flash loan parameter authentication
    bytes32 private _flashLoanArgsHash = 0;
    // The Deployed or Undeployed pending amount. Used for internal accounting
    uint256 private _pendingAmount = 0;

    /**
     * @dev Internal function to initialize the AAVEv3 strategy base.
     *
     * This function is used for the initial setup of the AAVEv3 strategy base contract, including ownership transfer,
     * service registry initialization, setting oracles, configuring AAVEv3 parameters, and approving allowances.
     *
     * @param initialOwner The address to be set as the initial owner of the AAVEv3 strategy base contract.
     * @param collateralToken The hash representing the collateral ERC20 token in the service registry.
     * @param debtToken The hash representing the collateral/ETH oracle in the service registry.
     * @param oracle The hash representing the collateral ERC20 token in the service registry.
     * @param flashLender The hash representing the flash lender in the service registry.
     *
     * Requirements:
     * - The caller must be in the initializing state.
     * - The initial owner address must not be the zero address.
     * - The debt/USD oracle and collateral/USD oracle addresses must be valid.
     * - Approval allowances must be successfully set for debt ERC20 and the collateral ERC20 token for UniSwap.
     */
    function _initializeStrategyLeverage(
        address initialOwner,
        address initialGovernor,
        address collateralToken,
        address debtToken,
        address oracle,
        address flashLender
    ) internal onlyInitializing {
        if (initialOwner == address(0)) revert InvalidOwner();

        _initLeverageSettings(initialOwner, initialGovernor);
        _initUseFlashLender(flashLender);

        // Find the Tokens on Registry
        _collateralToken = collateralToken;
        _debtToken = debtToken;

        // Set the Oracle
        _oracle = IOracle(oracle);

        if (_collateralToken == address(0)) revert InvalidCollateralToken();
        if (_debtToken == address(0)) revert InvalidDebtToken();

        if (address(_oracle) == address(0)) revert InvalidOracle();
    }

    /**
     * @dev Fallback function to receive Ether.
     *
     *  This function is automatically called when the contract receives Ether
     *  without a specific function call.
     *
     *  It allows the contract to accept incoming Ether fromn the WETH contract
     */
    receive() external payable {
        if (msg.sender != _debtToken && msg.sender != _collateralToken) revert ETHTransferNotAllowed(msg.sender);
    }

    /**
     * @dev Retrieves the position details including total collateral, total debt, and loan-to-value ratio.
     *
     * This function is externally callable and returns the total collateral in Ether, total debt in USD,
     * and the loan-to-value ratio for the AAVEv3 strategy.
     *
     * @return totalCollateralInAsset The total collateral in USD.
     * @return totalDebtInAsset The total debt in USD.
     * @return loanToValue The loan-to-value ratio calculated as (totalDebtInUSD * PERCENTAGE_PRECISION) / totalCollateralInUSD.
     *
     * Requirements:
     * - The AAVEv3 strategy must be properly configured and initialized.
     */
    function getPosition(
        IOracle.PriceOptions memory priceOptions
    ) external view returns (uint256 totalCollateralInAsset, uint256 totalDebtInAsset, uint256 loanToValue) {
        (totalCollateralInAsset, totalDebtInAsset) = _getPosition(priceOptions);
        if (totalCollateralInAsset == 0) {
            loanToValue = 0;
        } else {
            loanToValue = (totalDebtInAsset * PERCENTAGE_PRECISION) / totalCollateralInAsset;
        }
    }

    /**
     * @dev Retrieves the total owned assets by the Strategy in USD
     *
     * This function is externally callable and returns the total owned assets in USD, calculated as the difference
     * between total collateral and total debt. If the total collateral is less than or equal to the total debt, the
     * total owned assets is set to 0.
     *
     * @return totalOwnedAssetsInDebt The total owned assets in Debt Token
     *
     * Requirements:
     * - The AAVEv3 strategy must be properly configured and initialized.
     */
    function totalAssets() external view returns (uint256 totalOwnedAssetsInDebt) {
        IOracle.PriceOptions memory priceOptions = IOracle.PriceOptions({maxAge: 0, maxConf: 0});
        (uint256 totalCollateral, uint256 totalDebt) = getBalances();
        uint256 totalCollateralInDebt = _toDebt(priceOptions, totalCollateral, false);
        totalOwnedAssetsInDebt = totalCollateralInDebt > totalDebt ? (totalCollateralInDebt - totalDebt) : 0;
    }

    /**
     * @dev Deploys funds in the AAVEv3 strategy
     *
     * This function is externally callable only by the owner, and it involves the following steps:
     * 1. Transfer the Debt Token to the Strategy
     * 2. Initiates a Debt Token flash loan to leverage the deposited amount.
     *
     * @return deployedAmount The amount deployed in the AAVEv3 strategy after leveraging.
     *
     * Requirements:
     * - The caller must be the owner of the contract.
     * - The received Ether amount must not be zero.
     * - The AAVEv3 strategy must be properly configured and initialized.
     */
    function deploy(uint256 amount) external onlyOwner nonReentrant returns (uint256 deployedAmount) {
        // Ensure a non-zero deployment amount
        if (amount == 0) revert InvalidDeployAmount();

        // 1. Transfer assets from the vault to the contract
        IERC20Upgradeable(_debtToken).safeTransferFrom(msg.sender, address(this), amount);

        // 2. Calculate leverage and determine the loan amount needed
        uint256 leverage = _calculateLeverageRatio(amount, getLoanToValue(), getNrLoops());
        uint256 loanAmount = leverage - amount;

        // 3. Calculate the flash loan fee for the required loan amount
        uint256 fee = flashLender().flashFee(_debtToken, loanAmount);

        // 4. Approve the flash lender to spend the loan amount plus fee
        if (!IERC20Upgradeable(_debtToken).approve(flashLenderA(), loanAmount + fee)) {
            revert FailedToApproveAllowance();
        }

        // 5. Prepare and authenticate flash loan data
        bytes memory data = abi.encode(amount, msg.sender, FlashLoanAction.SUPPLY_BORROW);
        _flashLoanArgsHash = keccak256(abi.encodePacked(address(this), _debtToken, loanAmount, data));

        // 6. Execute the flash loan
        if (!flashLender().flashLoan(IERC3156FlashBorrowerUpgradeable(this), _debtToken, loanAmount, data)) {
            _flashLoanArgsHash = 0;
            revert FailedToRunFlashLoan();
        }

        // 7. Reset flash loan argument hash and update deployed assets
        _flashLoanArgsHash = 0;
        deployedAmount = _pendingAmount;
        _deployedAssets += deployedAmount;

        // 8. Emit an event for the updated strategy amount
        emit StrategyAmountUpdate(_deployedAssets);

        // 9. Reset the pending amount to zero
        _pendingAmount = 0;
    }

    /**
     * @dev Handles the execution of actions after receiving a flash loan.
     *
     * This function is part of the IERC3156FlashBorrower interface and is called by the flash lender contract
     * after a flash loan is initiated. It validates the loan parameters, ensures that the initiator is the
     * contract itself, and executes specific actions based on the provided FlashLoanAction. The supported actions
     * include supplying and borrowing funds, repaying debt and withdrawing collateral, and simply repaying debt.
     * The function returns a bytes32 success message after the actions are executed.
     *
     * @param initiator The address that initiated the flash loan.
     * @param token The address of the token being flash borrowed (should be Debt Token in this case).
     * @param amount The total amount of tokens being flash borrowed.
     * @param fee The fee amount associated with the flash loan.
     * @param callData Additional data encoded for specific actions, including the original amount, action type, and receiver address.
     *
     * Requirements:
     * - The flash loan sender must be the expected flash lender contract.
     * - The initiator must be the contract itself to ensure trust.
     * - The contract must be properly configured and initialized.
     */
    function onFlashLoan(
        address initiator,
        address token,
        uint256 amount,
        uint256 fee,
        bytes memory callData
    ) external returns (bytes32) {
        // Validate the flash loan sender
        if (msg.sender != flashLenderA()) revert InvalidFlashLoanSender();

        // Validate the flash loan initiator
        if (initiator != address(this)) revert InvalidLoanInitiator();

        // Ensure the token used is the debt token
        if (token != _debtToken) revert InvalidFlashLoanAsset();

        // Authenticate the provided arguments against the stored hash
        bytes32 expectedHash = keccak256(abi.encodePacked(initiator, token, amount, callData));
        if (_flashLoanArgsHash != expectedHash) revert FailedToAuthenticateArgs();

        // Decode the flash loan data
        FlashLoanData memory data = abi.decode(callData, (FlashLoanData));

        // Execute the appropriate action based on the decoded flash loan data
        if (data.action == FlashLoanAction.SUPPLY_BORROW) {
            _supplyBorrow(data.originalAmount, amount, fee);
        } else if (data.action == FlashLoanAction.PAY_DEBT_WITHDRAW) {
            _repayAndWithdraw(data.originalAmount, amount, fee, payable(data.receiver));
        } else if (data.action == FlashLoanAction.PAY_DEBT) {
            _payDebt(amount, fee);
        } else {
            revert InvalidFlashLoanAction();
        }

        return _SUCCESS_MESSAGE;
    }
    /**
     * @dev Initiates the undeployment of a specified amount, sending the resulting ETH to the contract owner.
     *
     * This function allows the owner of the contract to undeploy a specified amount, which involves
     * withdrawing the corresponding collateral, converting it to Debt Token, unwrapping Debt Token, and finally
     * sending the resulting ETH to the contract owner. The undeployment is subject to reentrancy protection.
     * The function returns the amount of ETH undeployed to the contract owner.
     * The method is designed to ensure that the collateralization ratio (collateral value to debt value) remains within acceptable limits.
     * It leverages a flash loan mechanism to obtain additional funds temporarily, covering any necessary adjustments required to maintain
     * the desired collateralization ratio.
     *
     * @param amount The amount of collateral to undeploy.
     *
     * Requirements:
     * - The caller must be the owner of the contract.
     */
    function undeploy(uint256 amount) external onlyOwner nonReentrant returns (uint256 undeployedAmount) {
        undeployedAmount = _undeploy(amount, payable(msg.sender));
    }

    /**
     * @notice Adjusts the current debt position by calculating the amount of debt to repay and executing a flash loan.
     * @dev The function calculates the necessary debt to repay based on the loan-to-value (LTV) ratio and initiates a flash loan
     *      to cover this amount. The function also handles the approval for the flash loan and manages the flash loan execution.
     * @param totalCollateralInDebt The total collateral value expressed in debt terms.
     * @param totalDebt The current total debt amount.
     * @return deltaAmount The total amount of debt adjusted, including any flash loan fees.
     */
    function _adjustDebt(uint256 totalCollateralInDebt, uint256 totalDebt) internal returns (uint256 deltaAmount) {
        // Calculate the debt amount to repay to reach the desired Loan-to-Value (LTV) ratio
        uint256 deltaDebt = _calculateDebtToPay(getLoanToValue(), totalCollateralInDebt, totalDebt);

        // Calculate the flash loan fee for the debt amount
        uint256 fee = flashLender().flashFee(_debtToken, deltaDebt);

        // Prepare data for the flash loan execution
        bytes memory data = abi.encode(deltaDebt, address(0), FlashLoanAction.PAY_DEBT);

        // Approve the flash lender to spend the debt amount plus fee
        if (!IERC20Upgradeable(_debtToken).approve(flashLenderA(), deltaDebt + fee)) {
            revert FailedToApproveAllowance();
        }

        // Set a unique hash for the flash loan arguments to prevent reentrancy attacks
        _flashLoanArgsHash = keccak256(abi.encodePacked(address(this), _debtToken, deltaDebt, data));

        // Execute the flash loan for the calculated debt amount
        if (!flashLender().flashLoan(IERC3156FlashBorrowerUpgradeable(this), _debtToken, deltaDebt, data)) {
            _flashLoanArgsHash = 0;
            revert FailedToRunFlashLoan();
        }

        // Reset the hash after successful flash loan execution
        _flashLoanArgsHash = 0;

        // Return the total amount adjusted, including the flash loan fee
        deltaAmount = deltaDebt + fee;
    }

    /**
     * @dev Harvests the strategy by rebalancing the collateral and debt positions.
     *
     * This function allows the owner of the contract to harvest the strategy by rebalancing the collateral
     * and debt positions. It calculates the current collateral and debt positions, checks if the collateral
     * is higher than the debt, adjusts the debt if needed to maintain the loan-to-value (LTV) within the specified
     * range, and logs profit or loss based on changes in the deployed amount. The function returns the balance change
     * as an int256 value.
     *
     * Requirements:
     * - The caller must be the owner of the contract.
     * - The contract must be properly configured and initialized.
     *
     * Emits:
     * - StrategyProfit: If the strategy achieves a profit.
     * - StrategyLoss: If the strategy incurs a loss.
     * - StrategyAmountUpdate: Whenever the deployed amount is updated.
     *
     * @return balanceChange The change in strategy balance as an int256 value.
     */
    function harvest() external override onlyOwner nonReentrant returns (int256 balanceChange) {
        // Fetch leverage balances
        (uint256 totalCollateral, uint256 totalDebt) = getBalances();

        // Convert total collateral to debt value using Oracle
        uint256 totalCollateralInDebt = _toDebt(
            IOracle.PriceOptions({maxAge: getPriceMaxAge(), maxConf: getPriceMaxConf()}),
            totalCollateral,
            false
        );

        // Early exit conditions
        if (totalCollateralInDebt == 0 || totalDebt == 0) {
            return 0;
        }
        if (totalCollateralInDebt <= totalDebt) {
            revert CollateralLowerThanDebt();
        }

        uint256 deployedAmount = _deployedAssets;
        uint256 deltaDebt = 0;

        // Calculate Loan-to-Value ratio
        uint256 ltv = (totalDebt * PERCENTAGE_PRECISION) / totalCollateralInDebt;

        // Adjust debt if LTV exceeds the maximum allowed
        if (ltv > getMaxLoanToValue() && ltv < PERCENTAGE_PRECISION) {
            deltaDebt = _adjustDebt(totalCollateralInDebt, totalDebt);
        }

        uint256 newDeployedAmount = totalCollateralInDebt - totalDebt;

        // Ensure valid debt adjustment
        if (deltaDebt >= totalCollateralInDebt) {
            revert InvalidDeltaDebt();
        }
        // If no change in deployed amount, return early
        if (newDeployedAmount == deployedAmount) {
            return 0;
        }

        // Log profit or loss based on the new deployed amount
        if (deltaDebt == 0) {
            if (newDeployedAmount > deployedAmount) {
                uint256 profit = newDeployedAmount - deployedAmount;
                emit StrategyProfit(profit);
                balanceChange = int256(profit);
            } else {
                uint256 loss = deployedAmount - newDeployedAmount;
                emit StrategyLoss(loss);
                balanceChange = -int256(loss);
            }
        }

        // Update deployed assets
        _deployedAssets = newDeployedAmount;
        emit StrategyAmountUpdate(newDeployedAmount);
    }

    /**
     * Get the Money Market Position Balances (Collateral, Debt) in Token Balances
     *
     * @return collateralBalance
     * @return debtBalance
     */
    function getBalances() public view virtual returns (uint256 collateralBalance, uint256 debtBalance);

    /**
     * @dev Retrieves the current collateral and debt positions of the contract.
     *
     * This internal function provides a view into the current collateral and debt positions of the contract
     * by querying the Aave V3 protocol. It calculates the positions in ETH based on the current ETH/USD exchange rate.
     *
     * @return totalCollateralInAsset The total collateral position in ETH.
     * @return totalDebtInAsset The total debt position in ETH.
     */
    function _getPosition(
        IOracle.PriceOptions memory priceOptions
    ) internal view returns (uint256 totalCollateralInAsset, uint256 totalDebtInAsset) {
        totalCollateralInAsset = 0;
        totalDebtInAsset = 0;

        (uint256 collateralBalance, uint256 debtBalance) = getBalances();
        // Convert Collateral Balance to $USD safely
        if (collateralBalance != 0) {
            totalCollateralInAsset = _toDebt(priceOptions, collateralBalance, false);
        }
        // Convert DebtBalance to Debt in Asset Terms
        if (debtBalance != 0) {
            totalDebtInAsset = debtBalance;
        }
    }

    /**
     * @dev Initiates the undeployment process by adjusting the contract's position and performing a flash loan.
     *
     * This private function calculates the necessary adjustments to the contract's position to accommodate the requested
     * undeployment amount. It then uses a flash loan to perform the required operations, including paying off debt and
     * withdrawing ETH. The resulting undeployed amount is updated, and the contract's deployed amount is adjusted accordingly.
     *
     * @param amount The amount of Debt Token to Undeploy.
     * @param receiver The address to receive the undeployed Debt Token.
     * @return receivedAmount The actual undeployed amount of Debt Token.
     *
     * Requirements:
     * - The contract must have a collateral margin greater than the debt to initiate undeployment.
     */
    function _undeploy(uint256 amount, address receiver) private returns (uint256 receivedAmount) {
        // Get price options from settings
        IOracle.PriceOptions memory options = IOracle.PriceOptions({
            maxAge: getPriceMaxAge(),
            maxConf: getPriceMaxConf()
        });

        // Fetch collateral and debt balances
        (uint256 totalCollateralBalance, uint256 totalDebtBalance) = getBalances();
        uint256 totalCollateralInDebt = _toDebt(options, totalCollateralBalance, false);

        // Ensure the position is not in liquidation state
        if (totalCollateralInDebt <= totalDebtBalance) revert NoCollateralMarginToScale();

        // Calculate percentage to burn to accommodate the withdrawal
        uint256 percentageToBurn = (amount * PERCENTAGE_PRECISION) / (totalCollateralInDebt - totalDebtBalance);

        // Calculate delta position (collateral and debt)
        (uint256 deltaCollateralInDebt, uint256 deltaDebt) = _calcDeltaPosition(
            percentageToBurn,
            totalCollateralInDebt,
            totalDebtBalance
        );
        // Convert deltaCollateralInDebt to deltaCollateralAmount
        uint256 deltaCollateralAmount = _toCollateral(options, deltaCollateralInDebt, true);

        // Calculate flash loan fee
        uint256 fee = flashLender().flashFee(_debtToken, deltaDebt);

        // Approve the flash lender to spend the debt amount plus fee
        if (!IERC20Upgradeable(_debtToken).approve(flashLenderA(), deltaDebt + fee)) {
            revert FailedToApproveAllowance();
        }

        // Prepare data for flash loan execution
        bytes memory data = abi.encode(deltaCollateralAmount, receiver, FlashLoanAction.PAY_DEBT_WITHDRAW);
        _flashLoanArgsHash = keccak256(abi.encodePacked(address(this), _debtToken, deltaDebt, data));

        // Execute flash loan
        if (!flashLender().flashLoan(IERC3156FlashBorrowerUpgradeable(this), _debtToken, deltaDebt, data)) {
            _flashLoanArgsHash = 0;
            revert FailedToRunFlashLoan();
        }
        // The amount of Withdrawn minus the repay ampunt
        emit StrategyUndeploy(msg.sender, deltaCollateralInDebt - deltaDebt);

        // Reset hash after successful flash loan
        _flashLoanArgsHash = 0;

        // Update deployed assets after withdrawal
        receivedAmount = _pendingAmount;
        uint256 undeployedAmount = deltaCollateralInDebt - deltaDebt;
        _deployedAssets = _deployedAssets > undeployedAmount ? _deployedAssets - undeployedAmount : 0;

        // Emit strategy update and reset pending amount
        emit StrategyAmountUpdate(_deployedAssets);
        // Pending amount is not cleared to save gas
        //_pendingAmount = 0;
    }

    /**
     * @dev Repays the debt on AAVEv3 strategy, handling the withdrawal and swap operations.
     *
     * This private function is used internally to repay the debt on the AAVEv3 strategy. It involves repaying
     * the debt on AAVE, obtaining a quote for the required collateral, withdrawing the collateral from AAVE, and
     * swapping the collateral to obtain the necessary Debt Token. The leftover Debt Token after the swap is deposited back
     * into AAVE if there are any. The function emits the `StrategyUndeploy` event after the debt repayment.
     *
     * @param debtAmount The amount of Debt Token to be repaid on AAVE.
     * @param fee The fee amount in Debt Token associated with the debt repayment.
     *
     * Requirements:
     * - The AAVEv3 strategy must be properly configured and initialized.
     */
    function _payDebt(uint256 debtAmount, uint256 fee) internal {
        // Repay the debt
        _repay(debtAmount);

        // Fetch price options from settings
        IOracle.PriceOptions memory options = IOracle.PriceOptions({
            maxAge: getPriceMaxAge(),
            maxConf: getPriceMaxConf()
        });

        // Calculate the equivalent collateral amount for the debt
        uint256 collateralAmount = _toCollateral(options, debtAmount, true);

        // Calculate maximum collateral required with slippage
        uint256 amountInMax = (collateralAmount * (PERCENTAGE_PRECISION + getMaxSlippage())) / PERCENTAGE_PRECISION;

        // Withdraw the collateral needed for the swap
        _withdraw(amountInMax, address(this));

        // Perform the swap to convert collateral into debt token
        (uint256 amountIn, ) = swap(
            ISwapHandler.SwapParams(
                _collateralToken,
                _debtToken,
                ISwapHandler.SwapType.EXACT_OUTPUT,
                amountInMax,
                debtAmount + fee,
                bytes("")
            )
        );

        // If there's leftover collateral after the swap, redeposit it
        if (amountIn < amountInMax) {
            uint256 swapLeftover = amountInMax - amountIn;
            _supply(swapLeftover);
        }

        // Emit event for strategy undeployment
        emit StrategyUndeploy(msg.sender, debtAmount);
    }

    /**
     * @dev Internal function to convert the specified amount from Debt Token to the underlying collateral asset cbETH, wstETH, rETH.
     *
     * This function is virtual and intended to be overridden in derived contracts for customized implementation.
     *
     * @param amount The amount to convert from debtToken.
     * @return uint256 The converted amount in the underlying collateral.
     */
    function _convertToCollateral(uint256 amount) internal virtual returns (uint256) {
        uint256 amountOutMinimum = 0;

        if (getMaxSlippage() > 0) {
            uint256 wsthETHAmount = _toCollateral(
                IOracle.PriceOptions({maxAge: getPriceMaxAge(), maxConf: getPriceMaxConf()}),
                amount,
                false
            );
            amountOutMinimum = (wsthETHAmount * (PERCENTAGE_PRECISION - getMaxSlippage())) / PERCENTAGE_PRECISION;
        }
        // 1. Swap Debt Token -> Collateral Token
        (, uint256 amountOut) = swap(
            ISwapHandler.SwapParams(
                _debtToken, // Asset In
                _collateralToken, // Asset Out
                ISwapHandler.SwapType.EXACT_INPUT, // Swap Mode
                amount, // Amount In
                amountOutMinimum, // Amount Out
                bytes("") // User Payload
            )
        );
        return amountOut;
    }

    /**
     * @dev Internal function to convert the specified amount to Debt Token from the underlying collateral.
     *
     * This function is virtual and intended to be overridden in derived contracts for customized implementation.
     *
     * @param amount The amount to convert to Debt Token.
     * @return uint256 The converted amount in Debt Token.
     */
    function _convertToDebt(uint256 amount) internal virtual returns (uint256) {
        uint256 amountOutMinimum = 0;
        if (getMaxSlippage() > 0) {
            uint256 ethAmount = _toDebt(
                IOracle.PriceOptions({maxAge: getPriceMaxAge(), maxConf: getPriceMaxConf()}),
                amount,
                false
            );
            amountOutMinimum = (ethAmount * (PERCENTAGE_PRECISION - getMaxSlippage())) / PERCENTAGE_PRECISION;
        }
        // 1.Swap Colalteral -> Debt Token
        (, uint256 amountOut) = swap(
            ISwapHandler.SwapParams(
                _collateralToken, // Asset In
                _debtToken, // Asset Out
                ISwapHandler.SwapType.EXACT_INPUT, // Swap Mode
                amount, // Amount In
                amountOutMinimum, // Amount Out
                bytes("") // User Payload
            )
        );
        return amountOut;
    }

    /**
     * @dev Internal function to convert the specified amount from Collateral Token to Debt Token.
     *
     * This function calculates the equivalent amount in Debt Tokeb based on the latest price from the collateral oracle.
     *
     * @param amountIn The amount in the underlying collateral.
     * @return amountOut The equivalent amount in Debt Token.
     */
    function _toDebt(
        IOracle.PriceOptions memory priceOptions,
        uint256 amountIn,
        bool roundUp
    ) internal view returns (uint256 amountOut) {
        amountOut = amountIn.mulDiv(_oracle.getSafeLatestPrice(priceOptions).price, _oracle.getPrecision(), roundUp);
    }

    /**
     * @dev Internal function to convert the specified amount from Debt Token to Collateral Token.
     *
     * This function calculates the equivalent amount in the underlying collateral based on the latest price from the collateral oracle.
     *
     * @param amountIn The amount in Debt Token to be converted.
     * @return amountOut The equivalent amount in the underlying collateral.
     */
    function _toCollateral(
        IOracle.PriceOptions memory priceOptions,
        uint256 amountIn,
        bool roundUp
    ) internal view returns (uint256 amountOut) {
        amountOut = amountIn.mulDiv(_oracle.getPrecision(), _oracle.getSafeLatestPrice(priceOptions).price, roundUp);
    }

    /**
     * @dev Executes the supply and borrow operations on AAVE, converting assets from Debt Token.
     *
     * This function is private and is used internally in the AAVEv3 strategy for depositing collateral
     * and borrowing ETH on the AAVE platform. It involves converting assets from Debt Tokens to the respective
     * tokens, supplying collateral, and borrowing ETH. The strategy owned value is logged on the  `StrategyDeploy` event.
     *
     * @param amount The amount to be supplied to AAVE (collateral) in Debt Token.
     * @param loanAmount The amount to be borrowed from AAVE in Debt Token.
     * @param fee The fee amount in Debt Token associated with the flash loan.
     *
     * Requirements:
     * - The AAVEv3 strategy must be properly configured and initialized.
     */
    function _supplyBorrow(uint256 amount, uint256 loanAmount, uint256 fee) internal {
        uint256 collateralIn = _convertToCollateral(amount + loanAmount);
        // Deposit on AAVE Collateral and Borrow Debt Token
        _supplyAndBorrow(collateralIn, loanAmount + fee);
        uint256 collateralInDebt = _toDebt(
            IOracle.PriceOptions({maxAge: getPriceMaxAge(), maxConf: getPriceMaxConf()}),
            collateralIn,
            false
        );
        uint256 deployedAmount = collateralInDebt - loanAmount - fee;
        _pendingAmount = deployedAmount;
        emit StrategyDeploy(msg.sender, deployedAmount);
    }

    /**
     * @dev Repays a specified amount, withdraws collateral, and sends the remaining Debt Token to the specified receiver.
     *
     * This private function is used internally to repay a specified amount on AAVE, withdraw collateral, and send
     * the remaining ETH to the specified receiver. It involves checking the available balance, repaying the debt on
     * AAVE, withdrawing the specified amount of collateral, converting collateral to Debt Token, unwrapping Debt Token, and finally
     * sending the remaining ETH to the receiver. The function emits the `StrategyUndeploy` event after the operation.
     *
     * @param withdrawAmount The amount of collateral balance to be withdraw.
     * @param repayAmount The amount of debt balance be repaid on AAVE.
     * @param fee The fee amount in debt balance to be paid as feed
     * @param receiver The address to receive the remaining debt tokens after debt repayment and withdrawal.
     *
     * Requirements:
     * - The AAVEv3 strategy must be properly configured and initialized.
     */
    function _repayAndWithdraw(
        uint256 withdrawAmount,
        uint256 repayAmount,
        uint256 fee,
        address payable receiver
    ) internal {
        (uint256 collateralBalance, ) = getBalances();
        uint256 cappedWithdrawAmount = collateralBalance < withdrawAmount ? collateralBalance : withdrawAmount;

        _repay(repayAmount);
        _withdraw(cappedWithdrawAmount, address(this));

        uint256 withdrawnAmount = _convertToDebt(cappedWithdrawAmount);
        uint256 debtToWithdraw = withdrawnAmount > (repayAmount + fee) ? withdrawnAmount - (repayAmount + fee) : 0;

        if (debtToWithdraw > 0) {
            IERC20Upgradeable(_debtToken).safeTransfer(receiver, debtToWithdraw);
        }

        _pendingAmount = debtToWithdraw;
    }

    /**
     * Money Market Functions
     *
     * The derived and money market specific classes should implement these functions to
     * be used on a Leverage Strategy.
     */

    /**
     *  @dev Deposit an asset assetIn on a money market
     */
    function _supply(uint256 amountIn) internal virtual;

    /**
     * @dev Deposit and borrow and asset using the asset deposited as collateral
     */
    function _supplyAndBorrow(uint256 amountIn, uint256 borrowOut) internal virtual;

    /**
     *  @dev Repay any borrow debt
     */
    function _repay(uint256 amount) internal virtual;

    /**
     * @dev  Withdraw a deposited asset from a money market
     *
     * @param amount The amoun to withdraw
     * @param to the account that will receive the asset
     */
    function _withdraw(uint256 amount, address to) internal virtual;

    /**
     * @dev
     */
    function renounceOwnership() public virtual override {
        revert InvalidOwner();
    }

    function getCollateralOracle() public view returns (address oracle) {
        oracle = address(_oracle);
    }

    function setDebtOracle(IOracle oracle) public onlyGovernor {
        _oracle = oracle;
    }

    function asset() public view override returns (address) {
        return _debtToken;
    }

    function getCollateralAsset() external view returns (address) {
        return _collateralToken;
    }

    function getDebAsset() external view returns (address) {
        return _debtToken;
    }
    /**
     * @dev This empty reserved space is put in place to allow future versions to add new
     * settings without shifting down storage in the inheritance chain.
     */
    uint256[25] private __gap;
}

