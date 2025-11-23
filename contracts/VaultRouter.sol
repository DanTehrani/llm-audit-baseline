// SPDX-License-Identifier: BUSL-1.1
pragma solidity =0.8.24;

// contracts/core/router/Commands.sol

/// @title Commands
/// @notice Command Flags used to decode commands
library Commands {
    // General Commands
    // Command identifiers for various actions within the protocol.

    // Uniswap V3 Swap Command
    uint8 public constant V3_UNISWAP_SWAP = 0x01; // Command to execute a swap on Uniswap V3.

    // Token Management Commands
    uint8 public constant PULL_TOKEN = 0x02; // Command to pull a specified token.
    uint8 public constant PULL_TOKEN_FROM = 0x03; // Command to pull a token from a specified address.
    uint8 public constant PUSH_TOKEN = 0x04; // Command to push a specified token.
    uint8 public constant PUSH_TOKEN_FROM = 0x05; // Command to push a token from a specified address.
    uint8 public constant SWEEP_TOKENS = 0x06; // Command to sweep tokens from the contract.
    uint8 public constant WRAP_ETH = 0x07; // Command to wrap ETH into WETH.
    uint8 public constant UNWRAP_ETH = 0x08; // Command to unwrap WETH back into ETH.
    uint8 public constant PULL_TOKEN_WITH_PERMIT = 0x09; // Command to pull a token using a permit.

    // ERC4626 Vault Commands
    uint8 public constant ERC4626_VAULT_DEPOSIT = 0x10; // Command to deposit assets into an ERC4626 vault.
    uint8 public constant ERC4626_VAULT_MINT = 0x11; // Command to mint shares in an ERC4626 vault.
    uint8 public constant ERC4626_VAULT_REDEEM = 0x12; // Command to redeem shares from an ERC4626 vault.
    uint8 public constant ERC4626_VAULT_WITHDRAW = 0x13; // Command to withdraw assets from an ERC4626 vault.
    uint8 public constant ERC4626_VAULT_CONVERT_TO_SHARES = 0x14; // Command to convert assets to shares in an ERC4626 vault.
    uint8 public constant ERC4626_VAULT_CONVERT_TO_ASSETS = 0x15; // Command to convert shares to assets in an ERC4626 vault.

    uint8 public constant AERODROME_SWAP = 0x20; // Command to execute a swap on Aerodrome.
    uint8 public constant V2_UNISWAP_SWAP = 0x21; // Command to execute a swap on Aerodrome.

    // Constant for a 32-bit mask used in bitwise operations.
    uint32 public constant THIRTY_TWO_BITS_MASK = 0xFFFFFFFF; // Mask to extract 32 bits.

    // Errors
    error InvalidMappingIndex(uint8 index);

    error InvalidPosition(uint8 position);
    // 8 bits
    uint8 constant INDEX_SLOT_SIZE = 8;
    // Statically define the call stack size
    uint256 constant CALL_STACK_SIZE = 8;
    // Slot Mask
    uint8 constant INDEX_SLOT_MASK = 0xFF;

    /**
     * @notice Pull a value from the call stack or the value if the index is 0
     * @param callStack The call stack
     * @param value The value to pull
     * @param inputMapping The input mapping containing 8 slots of 8 bits each
     * @param position The position to extract from inputMapping (1-8)
     * @return result The result
     * @dev Bit operations:
     *   1. inputMapping >> (INDEX_SLOT_SIZE * position): Right shifts the inputMapping by position * 8 bits
     *      to align the desired 8-bit slot to the rightmost position
     *   2. & INDEX_SLOT_MASK (0xFF): Masks off all bits except the rightmost 8 bits
     *      to extract just the 8-bit index value we want
     *   Example:
     *   If inputMapping = 0x0000000000000321 and position = 1
     *   1. 0x0000000000000321 >> (8 * 1) = 0x0000000000000003
     *   2. 0x0000000000000003 & 0xFF = 0x03 (final index value)
     */
    function pullInputParam(
        uint256[] memory callStack,
        uint256 value,
        uint64 inputMapping,
        uint8 position
    ) internal pure returns (uint256 result) {
        if (position > CALL_STACK_SIZE) {
            revert InvalidPosition({position: position});
        }
        uint8 inputIndex = uint8(((inputMapping >> (INDEX_SLOT_SIZE * (position - 1))) & INDEX_SLOT_MASK));
        if (inputIndex > CALL_STACK_SIZE) {
            revert InvalidMappingIndex({index: inputIndex});
        }
        result = inputIndex > 0 ? callStack[inputIndex - 1] : value;
    }

    /**
     * @notice Push a value to the call stack if the index is not 0
     * @param callStack The call stack
     * @param value The value to push
     * @param outputMapping The output mapping containing 8 slots of 8 bits each
     * @param position The position to extract from outputMapping (1-8)
     * @dev Bit operations:
     *   1. outputMapping >> (INDEX_SLOT_SIZE * position): Right shifts the outputMapping by position * 8 bits
     *      to align the desired 8-bit slot to the rightmost position
     *   2. & INDEX_SLOT_MASK (0xFF): Masks off all bits except the rightmost 8 bits
     *      to extract just the 8-bit index value we want
     *   Example:
     *   If outputMapping = 0x0000000000000321 and position = 1
     *   1. 0x0000000000000321 >> (8 * 1) = 0x0000000000000003
     *   2. 0x0000000000000003 & 0xFF = 0x03 (final index value)
     */
    function pushOutputParam(
        uint256[] memory callStack,
        uint256 value,
        uint64 outputMapping,
        uint8 position
    ) internal pure {
        if (position > CALL_STACK_SIZE) {
            revert InvalidPosition({position: position});
        }
        uint8 outputIndex = uint8(((outputMapping >> (INDEX_SLOT_SIZE * (position - 1))) & INDEX_SLOT_MASK));
        if (outputIndex > CALL_STACK_SIZE) {
            revert InvalidMappingIndex({index: outputIndex});
        }
        if (outputIndex > 0) {
            callStack[outputIndex - 1] = value;
        }
    }
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

// contracts/core/MultiCommand.sol

/**
 * @notice A command is a single action to be executed within a sequence of commands.
 */
struct Command {
    // bits (0-32) is the action
    // bits (32-63) is the Input Mapping
    // bits (64-95) are the Output Mapping
    // bits (96-255) are reserved for future use.
    uint256 action;
    // Action Arguments
    // the encoded arguments for the action
    bytes data;
}

/**
 * @title IMultiCommand Inspired in Uniswap's MultiCall
 *
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 * @author Chef Kal-EL <chef.kal-el@bakerfi.xyz>
 *
 * @notice This contract provides a way to execute multiple commands within a single call.
 * It allows for the execution of a sequence of commands, each with its own action and data.
 * If any of the commands fail, the entire execution is reverted and an error is thrown.
 *
 * @dev This contract is designed to be inherited by other contracts that need to execute multiple commands.
 * It provides a way to dispatch individual commands and execute a sequence of commands.
 * The `msg.value` should not be trusted for any method callable from multicall.
 */
abstract contract MultiCommand {
    /// @notice The call stack size

    /**
     * @notice ExecutionFailed
     * @param commandIndex The index of the command that failed execution.
     * @param message The error message from the failed command execution.
     */
    error ExecutionFailed(uint256 commandIndex, bytes message);

    /**
     * @notice InvalidCommand
     * @param action The action of the command that is invalid.
     */
    error InvalidCommand(uint256 action);

    /**
     * @notice Dispatches a single command for execution.
     * @param action The command to be dispatched.
     * @param data The command to be dispatched.
     * @return success A boolean indicating if the command was executed successfully.
     * @return output The output data from the command execution.
     */
    function dispatch(
        uint256 action,
        bytes calldata data,
        uint256[] memory callStack
    ) internal virtual returns (bool success, bytes memory output);

    /**
   * @notice Executes a sequence of commands within the current contract.

   * @param commands The array of commands to be executed.
   * @dev This function iterates over the array of commands, dispatching each one for execution.
   * If any command fails, the entire execution is reverted and an error is thrown.
   *
   * @dev The call stack is reserved space for the call stack that is of 8 slots that could
   * be used during the execution to pull and push action outputs and inputs.
    */
    function execute(Command[] calldata commands) external payable {
        bytes memory output;
        bool success;
        uint256 numCommands = commands.length;
        // Reserve space for the call stack that is of 8 slots
        uint256[] memory callStack = new uint256[](Commands.CALL_STACK_SIZE);
        for (uint256 commandIndex = 0; commandIndex < numCommands; ) {
            (success, output) = dispatch(commands[commandIndex].action, commands[commandIndex].data, callStack);
            if (!success) {
                revert ExecutionFailed({commandIndex: commandIndex, message: output});
            }
            unchecked {
                commandIndex++;
            }
        }
    }
}

// contracts/interfaces/tokens/IWETH.sol

interface IWETH is IERC20 {
    function allowance(address, address) external view returns (uint256);

    function balanceOf(address) external view returns (uint256);

    function approve(address, uint256) external returns (bool success);

    function transfer(address, uint256) external returns (bool);

    function transferFrom(address, address, uint256) external returns (bool);

    function deposit() external payable;

    function withdraw(uint256) external;
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

// node_modules/@openzeppelin/contracts/interfaces/IERC20.sol

// OpenZeppelin Contracts v4.4.1 (interfaces/IERC20.sol)

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

// node_modules/@openzeppelin/contracts/interfaces/IERC4626.sol

// OpenZeppelin Contracts (last updated v4.9.0) (interfaces/IERC4626.sol)

/**
 * @dev Interface of the ERC4626 "Tokenized Vault Standard", as defined in
 * https://eips.ethereum.org/EIPS/eip-4626[ERC-4626].
 *
 * _Available since v4.7._
 */
interface IERC4626 is IERC20, IERC20Metadata {
    event Deposit(address indexed sender, address indexed owner, uint256 assets, uint256 shares);

    event Withdraw(
        address indexed sender,
        address indexed receiver,
        address indexed owner,
        uint256 assets,
        uint256 shares
    );

    /**
     * @dev Returns the address of the underlying token used for the Vault for accounting, depositing, and withdrawing.
     *
     * - MUST be an ERC-20 token contract.
     * - MUST NOT revert.
     */
    function asset() external view returns (address assetTokenAddress);

    /**
     * @dev Returns the total amount of the underlying asset that is “managed” by Vault.
     *
     * - SHOULD include any compounding that occurs from yield.
     * - MUST be inclusive of any fees that are charged against assets in the Vault.
     * - MUST NOT revert.
     */
    function totalAssets() external view returns (uint256 totalManagedAssets);

    /**
     * @dev Returns the amount of shares that the Vault would exchange for the amount of assets provided, in an ideal
     * scenario where all the conditions are met.
     *
     * - MUST NOT be inclusive of any fees that are charged against assets in the Vault.
     * - MUST NOT show any variations depending on the caller.
     * - MUST NOT reflect slippage or other on-chain conditions, when performing the actual exchange.
     * - MUST NOT revert.
     *
     * NOTE: This calculation MAY NOT reflect the “per-user” price-per-share, and instead should reflect the
     * “average-user’s” price-per-share, meaning what the average user should expect to see when exchanging to and
     * from.
     */
    function convertToShares(uint256 assets) external view returns (uint256 shares);

    /**
     * @dev Returns the amount of assets that the Vault would exchange for the amount of shares provided, in an ideal
     * scenario where all the conditions are met.
     *
     * - MUST NOT be inclusive of any fees that are charged against assets in the Vault.
     * - MUST NOT show any variations depending on the caller.
     * - MUST NOT reflect slippage or other on-chain conditions, when performing the actual exchange.
     * - MUST NOT revert.
     *
     * NOTE: This calculation MAY NOT reflect the “per-user” price-per-share, and instead should reflect the
     * “average-user’s” price-per-share, meaning what the average user should expect to see when exchanging to and
     * from.
     */
    function convertToAssets(uint256 shares) external view returns (uint256 assets);

    /**
     * @dev Returns the maximum amount of the underlying asset that can be deposited into the Vault for the receiver,
     * through a deposit call.
     *
     * - MUST return a limited value if receiver is subject to some deposit limit.
     * - MUST return 2 ** 256 - 1 if there is no limit on the maximum amount of assets that may be deposited.
     * - MUST NOT revert.
     */
    function maxDeposit(address receiver) external view returns (uint256 maxAssets);

    /**
     * @dev Allows an on-chain or off-chain user to simulate the effects of their deposit at the current block, given
     * current on-chain conditions.
     *
     * - MUST return as close to and no more than the exact amount of Vault shares that would be minted in a deposit
     *   call in the same transaction. I.e. deposit should return the same or more shares as previewDeposit if called
     *   in the same transaction.
     * - MUST NOT account for deposit limits like those returned from maxDeposit and should always act as though the
     *   deposit would be accepted, regardless if the user has enough tokens approved, etc.
     * - MUST be inclusive of deposit fees. Integrators should be aware of the existence of deposit fees.
     * - MUST NOT revert.
     *
     * NOTE: any unfavorable discrepancy between convertToShares and previewDeposit SHOULD be considered slippage in
     * share price or some other type of condition, meaning the depositor will lose assets by depositing.
     */
    function previewDeposit(uint256 assets) external view returns (uint256 shares);

    /**
     * @dev Mints shares Vault shares to receiver by depositing exactly amount of underlying tokens.
     *
     * - MUST emit the Deposit event.
     * - MAY support an additional flow in which the underlying tokens are owned by the Vault contract before the
     *   deposit execution, and are accounted for during deposit.
     * - MUST revert if all of assets cannot be deposited (due to deposit limit being reached, slippage, the user not
     *   approving enough underlying tokens to the Vault contract, etc).
     *
     * NOTE: most implementations will require pre-approval of the Vault with the Vault’s underlying asset token.
     */
    function deposit(uint256 assets, address receiver) external returns (uint256 shares);

    /**
     * @dev Returns the maximum amount of the Vault shares that can be minted for the receiver, through a mint call.
     * - MUST return a limited value if receiver is subject to some mint limit.
     * - MUST return 2 ** 256 - 1 if there is no limit on the maximum amount of shares that may be minted.
     * - MUST NOT revert.
     */
    function maxMint(address receiver) external view returns (uint256 maxShares);

    /**
     * @dev Allows an on-chain or off-chain user to simulate the effects of their mint at the current block, given
     * current on-chain conditions.
     *
     * - MUST return as close to and no fewer than the exact amount of assets that would be deposited in a mint call
     *   in the same transaction. I.e. mint should return the same or fewer assets as previewMint if called in the
     *   same transaction.
     * - MUST NOT account for mint limits like those returned from maxMint and should always act as though the mint
     *   would be accepted, regardless if the user has enough tokens approved, etc.
     * - MUST be inclusive of deposit fees. Integrators should be aware of the existence of deposit fees.
     * - MUST NOT revert.
     *
     * NOTE: any unfavorable discrepancy between convertToAssets and previewMint SHOULD be considered slippage in
     * share price or some other type of condition, meaning the depositor will lose assets by minting.
     */
    function previewMint(uint256 shares) external view returns (uint256 assets);

    /**
     * @dev Mints exactly shares Vault shares to receiver by depositing amount of underlying tokens.
     *
     * - MUST emit the Deposit event.
     * - MAY support an additional flow in which the underlying tokens are owned by the Vault contract before the mint
     *   execution, and are accounted for during mint.
     * - MUST revert if all of shares cannot be minted (due to deposit limit being reached, slippage, the user not
     *   approving enough underlying tokens to the Vault contract, etc).
     *
     * NOTE: most implementations will require pre-approval of the Vault with the Vault’s underlying asset token.
     */
    function mint(uint256 shares, address receiver) external returns (uint256 assets);

    /**
     * @dev Returns the maximum amount of the underlying asset that can be withdrawn from the owner balance in the
     * Vault, through a withdraw call.
     *
     * - MUST return a limited value if owner is subject to some withdrawal limit or timelock.
     * - MUST NOT revert.
     */
    function maxWithdraw(address owner) external view returns (uint256 maxAssets);

    /**
     * @dev Allows an on-chain or off-chain user to simulate the effects of their withdrawal at the current block,
     * given current on-chain conditions.
     *
     * - MUST return as close to and no fewer than the exact amount of Vault shares that would be burned in a withdraw
     *   call in the same transaction. I.e. withdraw should return the same or fewer shares as previewWithdraw if
     *   called
     *   in the same transaction.
     * - MUST NOT account for withdrawal limits like those returned from maxWithdraw and should always act as though
     *   the withdrawal would be accepted, regardless if the user has enough shares, etc.
     * - MUST be inclusive of withdrawal fees. Integrators should be aware of the existence of withdrawal fees.
     * - MUST NOT revert.
     *
     * NOTE: any unfavorable discrepancy between convertToShares and previewWithdraw SHOULD be considered slippage in
     * share price or some other type of condition, meaning the depositor will lose assets by depositing.
     */
    function previewWithdraw(uint256 assets) external view returns (uint256 shares);

    /**
     * @dev Burns shares from owner and sends exactly assets of underlying tokens to receiver.
     *
     * - MUST emit the Withdraw event.
     * - MAY support an additional flow in which the underlying tokens are owned by the Vault contract before the
     *   withdraw execution, and are accounted for during withdraw.
     * - MUST revert if all of assets cannot be withdrawn (due to withdrawal limit being reached, slippage, the owner
     *   not having enough shares, etc).
     *
     * Note that some implementations will require pre-requesting to the Vault before a withdrawal may be performed.
     * Those methods should be performed separately.
     */
    function withdraw(uint256 assets, address receiver, address owner) external returns (uint256 shares);

    /**
     * @dev Returns the maximum amount of Vault shares that can be redeemed from the owner balance in the Vault,
     * through a redeem call.
     *
     * - MUST return a limited value if owner is subject to some withdrawal limit or timelock.
     * - MUST return balanceOf(owner) if owner is not subject to any withdrawal limit or timelock.
     * - MUST NOT revert.
     */
    function maxRedeem(address owner) external view returns (uint256 maxShares);

    /**
     * @dev Allows an on-chain or off-chain user to simulate the effects of their redeemption at the current block,
     * given current on-chain conditions.
     *
     * - MUST return as close to and no more than the exact amount of assets that would be withdrawn in a redeem call
     *   in the same transaction. I.e. redeem should return the same or more assets as previewRedeem if called in the
     *   same transaction.
     * - MUST NOT account for redemption limits like those returned from maxRedeem and should always act as though the
     *   redemption would be accepted, regardless if the user has enough shares, etc.
     * - MUST be inclusive of withdrawal fees. Integrators should be aware of the existence of withdrawal fees.
     * - MUST NOT revert.
     *
     * NOTE: any unfavorable discrepancy between convertToAssets and previewRedeem SHOULD be considered slippage in
     * share price or some other type of condition, meaning the depositor will lose assets by redeeming.
     */
    function previewRedeem(uint256 shares) external view returns (uint256 assets);

    /**
     * @dev Burns exactly shares from owner and sends assets of underlying tokens to receiver.
     *
     * - MUST emit the Withdraw event.
     * - MAY support an additional flow in which the underlying tokens are owned by the Vault contract before the
     *   redeem execution, and are accounted for during redeem.
     * - MUST revert if all of shares cannot be redeemed (due to withdrawal limit being reached, slippage, the owner
     *   not having enough shares, etc).
     *
     * NOTE: some implementations will require pre-requesting to the Vault before a withdrawal may be performed.
     * Those methods should be performed separately.
     */
    function redeem(uint256 shares, address receiver, address owner) external returns (uint256 assets);
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

// contracts/core/hooks/UsePermitTransfers.sol

abstract contract UsePermitTransfers {
    using SafeERC20 for IERC20;

    /**
     * @dev Allows the parent contractto pull tokens from the user using ERC20Permit.
     * @param token The address of the ERC20 token.
     * @param amount The amount of tokens to pull.
     * @param owner The address of the token owner.
     * @param deadline The deadline for the permit.
     * @param v The recovery byte of the signature.
     * @param r The output from the signing process (part of the signature).
     * @param s The output from the signing process (part of the signature).
     */
    function pullTokensWithPermit(
        IERC20Permit token,
        uint256 amount,
        address owner,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal virtual {
        // Permit the VaultRouter to spend tokens on behalf of the owner
        IERC20Permit(token).permit(owner, address(this), amount, deadline, v, r, s);

        // Transfer the tokens from the owner to this contract
        IERC20(address(token)).safeTransferFrom(owner, address(this), amount);
    }
}


// contracts/core/hooks/UseTokenActions.sol

/**
 * @title UseTokenActions
 *
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 * @author Chef Kal-EL <chef.kal-el@bakerfi.xyz>
 *
 * @notice This Hook provides functions to interact with ERC20 tokens and
 * could be included in other contracts to provide token actions.
 *
 */
abstract contract UseTokenActions is Initializable {
    using SafeERC20 for IERC20;

    /**
     * @dev Error thrown when an invalid token address is provided.
     */
    error InvalidToken();
    /**
     * @dev Error thrown when an invalid recipient address is provided.
     */
    error InvalidRecipient();
    /**
     * @dev Error thrown when the allowance is not enough.
     */
    error NotEnoughAllowance();

    /**
     * @dev Pulls a specified amount of tokens from the message sender to this contract.
     * @param token The ERC20 token to pull.
     * @param amount The amount of tokens to pull.
     */
    function pullToken(IERC20 token, uint256 amount) internal virtual {
        // Check if the token address is valid
        if (address(token) == address(0)) revert InvalidToken();

        if (token.allowance(msg.sender, address(this)) < amount) revert NotEnoughAllowance();
        // Use SafeERC20 to transfer tokens from the message sender to this contract
        IERC20(token).safeTransferFrom(msg.sender, address(this), amount);
    }

    /**
     * @dev Pulls a specified amount of tokens from a specified address to this contract.
     * @param token The ERC20 token to pull.
     * @param from The address from which to pull the tokens.
     * @param amount The amount of tokens to pull.
     */
    function pullTokenFrom(IERC20 token, address from, uint256 amount) internal virtual {
        // Check if the token address is valid
        if (address(token) == address(0)) revert InvalidToken();

        if (token.allowance(from, address(this)) < amount) revert NotEnoughAllowance();
        // Use SafeERC20 to transfer tokens from the specified address to this contract
        IERC20(token).safeTransferFrom(from, address(this), amount);
    }

    /**
     * @dev Pushes a specified amount of tokens from this contract to a specified address.
     * @param token The ERC20 token to push.
     * @param to The address to which to push the tokens.
     * @param amount The amount of tokens to push.
     */
    function pushToken(IERC20 token, address to, uint256 amount) internal virtual {
        // Check if the token address is valid
        if (address(token) == address(0)) revert InvalidToken();
        // Check if the recipient address is valid
        if (address(to) == address(0)) revert InvalidRecipient();
        // Use SafeERC20 to transfer tokens from this contract to the specified address
        IERC20(token).safeTransfer(to, amount);
    }

    /**
     * @dev Pushes a specified amount of tokens from a specified address to another specified address.
     * @param token The ERC20 token to push.
     * @param from The address from which to push the tokens.
     * @param to The address to which to push the tokens.
     * @param amount The amount of tokens to push.
     */
    function pushTokenFrom(IERC20 token, address from, address to, uint256 amount) internal virtual {
        // Check if the token address is valid
        if (address(token) == address(0)) revert InvalidToken();
        // Check if the recipient address is valid
        if (address(to) == address(0)) revert InvalidRecipient();

        if (token.allowance(from, address(this)) < amount) revert NotEnoughAllowance();
        // Use SafeERC20 to transfer tokens from the specified address to another specified address
        IERC20(token).safeTransferFrom(from, to, amount);
    }

    /**
     * @dev Sweeps all tokens from this contract to a specified address.
     * @param token The ERC20 token to sweep.
     * @param to The address to which to sweep the tokens.
     */
    function sweepTokens(IERC20 token, address to) internal virtual returns (uint256 sweptAmount) {
        // Check if the token address is valid
        if (address(token) == address(0)) revert InvalidToken();
        // Check if the recipient address is valid
        if (address(to) == address(0)) revert InvalidRecipient();
        // Use SafeERC20 to transfer tokens from this contract to the specified address
        sweptAmount = IERC20(token).balanceOf(address(this));

        IERC20(token).safeTransfer(to, sweptAmount);
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

// contracts/core/hooks/UseWETH.sol

/**
 * @title UseWETH
 *
 * @dev Abstract contract to integrate the use of Wrapped Ether (WETH).
 *      Provides functions to initialize, access, and unwrap WETH.
 *
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 * @author Chef Kal-El <chef.kal-el@bakerfi.xyz>
 */
abstract contract UseWETH is Initializable {
    using SafeERC20 for IERC20;

    error InvalidWETHContract();
    error FailedAllowance();
    error InvalidWETHAmount();
    error InsufficientWETHBalance();
    error ETHTransferNotAllowed(address sender);

    IWETH private _wETH;

    /**
     * @dev Initializes the UseWETH contract.
     * @param weth The address of the VaultRegistry contract for accessing WETH.
     */
    function _initUseWETH(address weth) internal onlyInitializing {
        _wETH = IWETH(weth);
        if (address(_wETH) == address(0)) revert InvalidWETHContract();
    }

    /**
     * @dev Fallback function to receive Ether.
     *
     * This function is marked as external and payable. It is automatically called
     * when Ether is sent to the contract, such as during a regular transfer or as part
     * of a self-destruct operation.
     *
     * Only Transfers from the strategy during the withdraw are allowed
     *
     * Emits no events and allows the contract to accept Ether.
     */
    receive() external payable virtual {}

    /**
     * @dev Returns the IWETH interface.
     * @return The IWETH interface.
     */
    function wETH() internal view returns (IWETH) {
        return _wETH;
    }

    /**
     * @dev Returns the address of the WETH contract.
     * @return The address of the WETH contract.
     */
    function wETHA() internal view returns (address) {
        return address(_wETH);
    }

    /**
     * @dev Unwraps a specified amount of WETH to Ether.
     * @param wETHAmount The amount of WETH to unwrap.
     */
    function unwrapETH(uint256 wETHAmount) internal virtual {
        // Validate the WETH amount to ensure it is non-zero
        if (wETHAmount == 0) revert InvalidWETHAmount();

        // Check if the contract has sufficient WETH balance to unwrap
        uint256 wETHBalance = _wETH.balanceOf(address(this));
        if (wETHBalance < wETHAmount) revert InsufficientWETHBalance();

        // Unwrap the specified amount of WETH to Ether
        wETH().withdraw(wETHAmount);
    }

    function wrapETH(uint256 amount) internal virtual {
        if (address(this).balance < amount) revert InvalidWETHAmount();

        wETH().deposit{value: amount}();
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

// contracts/core/hooks/UseIERC4626.sol

/**
 * @title UseIERC4626
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 * @author Chef Kal-El <chef.kal-el@bakerfi.xyz>
 *
 * @dev Contract to integrate the use of ERC4626 vaults.
 */
abstract contract UseIERC4626 is GovernableOwnable {
    /**
     * @dev Error thrown when an invalid vault address is provided.
     */
    error InvalidVaultAddress();
    error FailedToApproveAllowanceForVault();

    mapping(IERC4626 => mapping(IERC20 => bool)) private _approvedVaults;

    function initializeUseIERC4626(address initialOwner) internal onlyInitializing {
        _transferOwnership(initialOwner);
        _transferGovernorship(initialOwner);
    }

    function approveTokenForVault(IERC4626 vault, IERC20 token) public onlyGovernor {
        _approvedVaults[vault][token] = true;
        if (!IERC20(token).approve(address(vault), 2 ** 256 - 1)) revert FailedToApproveAllowanceForVault();
    }

    function isTokenApprovedForVault(IERC4626 vault, IERC20 token) public view returns (bool) {
        return _approvedVaults[vault][token];
    }

    function unapproveTokenForVault(IERC4626 vault, IERC20 token) public onlyGovernor {
        _approvedVaults[vault][token] = false;
        if (!IERC20(token).approve(address(vault), 0)) revert FailedToApproveAllowanceForVault();
    }

    /**
     * @dev Converts a specified amount of shares to assets within a vault.
     * @param vault The address of the ERC4626 vault.
     * @param shares The amount of shares to convert.
     * @return The amount of assets equivalent to the shares.
     */
    function convertToVaultAssets(IERC4626 vault, uint256 shares) internal view returns (uint256) {
        // Check if the vault address is valid
        if (address(vault) == address(0)) revert InvalidVaultAddress();
        // Call the convertToAssets function of the vault to convert shares to assets
        return vault.convertToAssets(shares);
    }

    /**
     * @dev Converts a specified amount of assets to shares within a vault.
     * @param vault The address of the ERC4626 vault.
     * @param assets The amount of assets to convert.
     * @return The amount of shares equivalent to the assets.
     */
    function convertToVaultShares(IERC4626 vault, uint256 assets) internal view returns (uint256) {
        // Check if the vault address is valid
        if (address(vault) == address(0)) revert InvalidVaultAddress();
        // Call the convertToShares function of the vault to convert assets to shares
        return vault.convertToShares(assets);
    }

    /**
     * @dev Returns the total amount of assets managed by a vault.
     * @param vault The address of the ERC4626 vault.
     * @return The total amount of assets managed by the vault.
     */
    function totalVaultAssets(IERC4626 vault) internal view virtual returns (uint256) {
        // Check if the vault address is valid
        if (address(vault) == address(0)) revert InvalidVaultAddress();
        // Call the totalAssets function of the vault to get the total assets
        return vault.totalAssets();
    }

    /**
     * @dev Returns the address of the asset token used by a vault.
     * @param vault The address of the ERC4626 vault.
     * @return The address of the asset token.
     */
    function vaultAsset(IERC4626 vault) internal view returns (address) {
        // Check if the vault address is valid
        if (address(vault) == address(0)) revert InvalidVaultAddress();
        // Call the asset function of the vault to get the asset token address
        return vault.asset();
    }

    /**
     * @dev Deposits a specified amount of assets into a vault for a receiver.
     * @param vault The address of the ERC4626 vault.
     * @param assets The amount of assets to deposit.
     * @param receiver The address to receive the shares.
     */
    function depositVault(IERC4626 vault, uint256 assets, address receiver) internal virtual returns (uint256 shares) {
        // Check if the vault address is valid
        if (address(vault) == address(0)) revert InvalidVaultAddress();
        // Call the deposit function of the vault to deposit assets
        shares = vault.deposit(assets, receiver);
    }

    /**
     * @dev Mints a specified amount of shares in a vault for a receiver.
     * @param vault The address of the ERC4626 vault.
     * @param shares The amount of shares to mint.
     * @param receiver The address to receive the shares.
     */
    function mintVault(IERC4626 vault, uint256 shares, address receiver) internal virtual returns (uint256 assets) {
        // Check if the vault address is valid
        if (address(vault) == address(0)) revert InvalidVaultAddress();
        // Call the mint function of the vault to mint shares
        assets = vault.mint(shares, receiver);
    }

    /**
     * @dev Withdraws a specified amount of assets from a vault to a receiver.
     * @param vault The address of the ERC4626 vault.
     * @param assets The amount of assets to withdraw.
     * @param receiver The address to receive the assets.
     * @param owner The owner of the shares.
     */
    function withdrawVault(
        IERC4626 vault,
        uint256 assets,
        address receiver,
        address owner
    ) internal virtual returns (uint256 shares) {
        // Call the withdraw function of the vault to withdraw assets
        shares = vault.withdraw(assets, receiver, owner);
    }

    /**
     * @dev Redeems a specified amount of shares in a vault for a receiver.
     * @param vault The address of the ERC4626 vault.
     * @param shares The amount of shares to redeem.
     * @param receiver The address to receive the assets.
     * @param owner The owner of the shares.
     */
    function redeemVault(
        IERC4626 vault,
        uint256 shares,
        address receiver,
        address owner
    ) internal virtual returns (uint256 assets) {
        // Check if the vault address is valid
        if (address(vault) == address(0)) revert InvalidVaultAddress();
        // Call the redeem function of the vault to redeem shares
        assets = vault.redeem(shares, receiver, owner);
    }
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


// contracts/core/VaultRouter.sol

/**
 * @title Vault Router inspired by Uniswap V3 Router
 *
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 * @author Chef Kal-EL <chef.kal-el@bakerfi.xyz>
 *
 * @notice This contract provides a router for vaults that allows for
 *   swapping between assets using Uniswap V3, migrate liquidity between
 *   protocols and deposit/withdraw from ERC4626 vaults.
 *
 * It also allows for multicall to execute multiple actions in a single call.
 *
 * Supports :
 * - Uniswap V3 exact input and exact output swaps.
 * - Wrapping and unwrapping WETH.
 * - Token transfers.
 * - ERC4626 vaults operations
 */
contract VaultRouter is UseUnifiedSwapper, UseTokenActions, UsePermitTransfers, UseIERC4626, UseWETH, MultiCommand {
    /// @notice Mapping of approved swap tokens
    mapping(IERC20 => bool) private _approvedSwapTokens;

    /// @custom:oz-upgrades-unsafe-allow constructor
    constructor() {
        _disableInitializers();
    }

    /**
     * @notice Initializes the contract.
     * @param initialOwner The address of the owner.
     * @param weth The Chain WETH address
     */
    function initialize(address initialOwner, IWETH weth) public initializer {
        initializeUseIERC4626(initialOwner);
        _initUseWETH(address(weth));
    }

    /**
     * @notice Dispatches a single command for execution.
     * @param action The command to be dispatched.
     * @param data The command to be dispatched.
     * @return success A boolean indicating if the command was executed successfully.
     * @return output The output data from the command execution.
     *
     * Action is a 256-bit value where:
     * The lower 32 bits represent the action to execute (actionToExecute).
     *   - The next 32 bits (bits 32-63) represent the input mapping (inputMapping).
     *     Each 8 bits in this range maps to an input parameter position.
     *
     *     Example: bits 32-33 represent the index of the first input parameter
     *
     *   - The next 32 bits (bits 64-95) represent the output mapping (outputMapping).
     *     Each 8 bits in this range maps to an output parameter position.
     *   - The remaining bits (96-255) are reserved for future use.
     *
     * The action parameter encodes multiple pieces of information in a compact format:
     * - The action ID determines which operation to perform
     * - Input/output mappings allow flexible parameter passing between commands
     * - Each 8-bit segment in the mappings corresponds to a parameter index
     *
     */
    function dispatch(
        uint256 action,
        bytes calldata data,
        uint256[] memory callStack
    ) internal override returns (bool success, bytes memory output) {
        success = true;
        // Extract the action ID from the lowest 32 bits using bitwise AND with mask
        uint32 actionToExecute = uint32(action & Commands.THIRTY_TWO_BITS_MASK);

        // Extract input mapping from bits 32-63 by right shifting 32 bits and masking
        uint32 inputMapping = uint16((action >> 32) & Commands.THIRTY_TWO_BITS_MASK);

        // Extract output mapping from bits 64-95 by right shifting 64 bits and masking
        uint32 outputMapping = uint16(((action >> 64) & Commands.THIRTY_TWO_BITS_MASK));

        if (
            actionToExecute == Commands.V3_UNISWAP_SWAP ||
            actionToExecute == Commands.AERODROME_SWAP ||
            actionToExecute == Commands.V2_UNISWAP_SWAP
        ) {
            output = _handleSwap(data, callStack, inputMapping, outputMapping);
        } else if (action == Commands.PULL_TOKEN) {
            output = _handlePullToken(data, callStack, inputMapping);
        } else if (actionToExecute == Commands.PULL_TOKEN_FROM) {
            output = _handlePullTokenFrom(data, callStack, inputMapping);
        } else if (actionToExecute == Commands.PUSH_TOKEN) {
            output = _handlePushToken(data, callStack, inputMapping);
        } else if (actionToExecute == Commands.PUSH_TOKEN_FROM) {
            output = _handlePushTokenFrom(data, callStack, inputMapping);
        } else if (actionToExecute == Commands.SWEEP_TOKENS) {
            output = _handleSweepTokens(data, callStack, outputMapping);
        } else if (actionToExecute == Commands.WRAP_ETH) {
            output = _handleWrapETH(data, callStack, inputMapping);
        } else if (actionToExecute == Commands.UNWRAP_ETH) {
            output = _handleUnwrapETH(data, callStack, inputMapping);
        } else if (actionToExecute == Commands.PULL_TOKEN_WITH_PERMIT) {
            output = _handlePullTokenWithPermit(data, callStack, inputMapping);
        } else if (actionToExecute == Commands.ERC4626_VAULT_DEPOSIT) {
            output = _handleVaultDeposit(data, callStack, inputMapping, outputMapping);
        } else if (actionToExecute == Commands.ERC4626_VAULT_MINT) {
            output = _handleVaultMint(data, callStack, inputMapping, outputMapping);
        } else if (actionToExecute == Commands.ERC4626_VAULT_REDEEM) {
            output = _handleVaultRedeem(data, callStack, inputMapping, outputMapping);
        } else if (actionToExecute == Commands.ERC4626_VAULT_WITHDRAW) {
            output = _handleVaultWithdraw(data, callStack, inputMapping, outputMapping);
        } else if (actionToExecute == Commands.ERC4626_VAULT_CONVERT_TO_SHARES) {
            output = _handleVaultConvertToShares(data, callStack, inputMapping, outputMapping);
        } else if (actionToExecute == Commands.ERC4626_VAULT_CONVERT_TO_ASSETS) {
            output = _handleVaultConvertToAssets(data, callStack, inputMapping, outputMapping);
        } else {
            revert InvalidCommand({action: action});
        }
    }

    /**
     * @notice Handles the Uniswap V3 swap command.
     * @param data The encoded swap parameters.
     * @param callStack The call stack.
     * @param inputMapping The input mapping.
     * @param outputMapping The output mapping.
     * @return output The encoded output values.
     */
    function _handleSwap(
        bytes calldata data,
        uint256[] memory callStack,
        uint32 inputMapping,
        uint32 outputMapping
    ) private returns (bytes memory) {
        ISwapHandler.SwapParams memory params = abi.decode(data, (ISwapHandler.SwapParams));
        params.amountIn = Commands.pullInputParam(callStack, params.amountIn, inputMapping, 1);
        params.amountOut = Commands.pullInputParam(callStack, params.amountOut, inputMapping, 2);

        (uint256 amountIn, uint256 amountOut) = swap(params);

        Commands.pushOutputParam(callStack, amountIn, outputMapping, 1);
        Commands.pushOutputParam(callStack, amountOut, outputMapping, 2);

        return abi.encodePacked(amountIn, amountOut);
    }
    /**
     * @notice Handles the pull token command.
     * @param data The encoded pull token parameters.
     * @param callStack The call stack.
     * @param inputMapping The input mapping.
     * @return output The encoded output values.
     */
    function _handlePullToken(
        bytes calldata data,
        uint256[] memory callStack,
        uint32 inputMapping
    ) private returns (bytes memory) {
        IERC20 token;
        uint256 amount;
        assembly {
            token := calldataload(data.offset)
            amount := calldataload(add(data.offset, 0x20))
        }
        amount = Commands.pullInputParam(callStack, amount, inputMapping, 1);
        pullToken(token, amount);
        return "";
    }
    /**
     * @notice Handles the pull token from command.
     * @param data The encoded pull token from parameters.
     * @param callStack The call stack.
     * @param inputMapping The input mapping.
     * @return output The encoded output values.
     */
    function _handlePullTokenFrom(
        bytes calldata data,
        uint256[] memory callStack,
        uint32 inputMapping
    ) private returns (bytes memory) {
        IERC20 token;
        address from;
        uint256 amount;
        assembly {
            token := calldataload(data.offset)
            from := calldataload(add(data.offset, 0x20))
            amount := calldataload(add(data.offset, 0x40))
        }
        amount = Commands.pullInputParam(callStack, amount, inputMapping, 1);
        pullTokenFrom(token, from, amount);
        return "";
    }
    /**
     * @notice Handles the push token command.
     * @param data The encoded push token parameters.
     * @param callStack The call stack.
     * @param inputMapping The input mapping.
     * @return output The encoded output values.
     */
    function _handlePushToken(
        bytes calldata data,
        uint256[] memory callStack,
        uint32 inputMapping
    ) private returns (bytes memory) {
        IERC20 token;
        address to;
        uint256 amount;
        assembly {
            token := calldataload(data.offset)
            to := calldataload(add(data.offset, 0x20))
            amount := calldataload(add(data.offset, 0x40))
        }
        amount = Commands.pullInputParam(callStack, amount, inputMapping, 1);
        pushToken(token, to, amount);
        return "";
    }
    /**
     * @notice Handles the push token from command.
     * @param data The encoded push token from parameters.
     * @param callStack The call stack.
     * @param inputMapping The input mapping.
     * @return output The encoded output values.
     */
    function _handlePushTokenFrom(
        bytes calldata data,
        uint256[] memory callStack,
        uint32 inputMapping
    ) private returns (bytes memory) {
        IERC20 token;
        address from;
        address to;
        uint256 amount;
        assembly {
            token := calldataload(data.offset)
            from := calldataload(add(data.offset, 0x20))
            to := calldataload(add(data.offset, 0x40))
            amount := calldataload(add(data.offset, 0x60))
        }
        amount = Commands.pullInputParam(callStack, amount, inputMapping, 1);
        pushTokenFrom(token, from, to, amount);
        return "";
    }
    /**
     * @notice Handles the sweep tokens command.
     * @param data The encoded sweep tokens parameters.
     * @param callStack The call stack.
     * @param outputMapping The output mapping.
     * @return output The encoded output values.
     */
    function _handleSweepTokens(
        bytes calldata data,
        uint256[] memory callStack,
        uint32 outputMapping
    ) private returns (bytes memory) {
        IERC20 token;
        address to;
        assembly {
            token := calldataload(data.offset)
            to := calldataload(add(data.offset, 0x20))
        }
        uint256 sweptAmount = sweepTokens(token, to);
        Commands.pushOutputParam(callStack, sweptAmount, outputMapping, 1);
        return abi.encodePacked(sweptAmount);
    }
    /**
     * @notice Handles the wrap ETH command.
     * @param data The encoded wrap ETH parameters.
     * @param callStack The call stack.
     * @param inputMapping The input mapping.
     * @return output The encoded output values.
     */
    function _handleWrapETH(
        bytes calldata data,
        uint256[] memory callStack,
        uint32 inputMapping
    ) private returns (bytes memory) {
        uint256 amount;
        assembly {
            amount := calldataload(data.offset)
        }
        amount = Commands.pullInputParam(callStack, amount, inputMapping, 1);
        wrapETH(amount);
        return "";
    }
    /**
     * @notice Handles the unwrap ETH command.
     * @param data The encoded unwrap ETH parameters.
     * @param callStack The call stack.
     * @param inputMapping The input mapping.
     * @return output The encoded output values.
     */
    function _handleUnwrapETH(
        bytes calldata data,
        uint256[] memory callStack,
        uint32 inputMapping
    ) private returns (bytes memory) {
        uint256 amount;
        assembly {
            amount := calldataload(data.offset)
        }
        amount = Commands.pullInputParam(callStack, amount, inputMapping, 1);
        unwrapETH(amount);
        return "";
    }
    /**
     * @notice Handles the pull token with permit command.
     * @param data The encoded pull token with permit parameters.
     * @param callStack The call stack.
     * @param inputMapping The input mapping.
     * @return output The encoded output values.
     */
    function _handlePullTokenWithPermit(
        bytes calldata data,
        uint256[] memory callStack,
        uint32 inputMapping
    ) private returns (bytes memory) {
        IERC20Permit token;
        uint256 amount;
        address owner;
        uint256 deadline;
        uint8 v;
        bytes32 r;
        bytes32 s;
        assembly {
            token := calldataload(data.offset)
            amount := calldataload(add(data.offset, 0x20))
            owner := calldataload(add(data.offset, 0x40))
            deadline := calldataload(add(data.offset, 0x60))
            v := calldataload(add(data.offset, 0x80))
            r := calldataload(add(data.offset, 0xa0))
            s := calldataload(add(data.offset, 0xc0))
        }
        amount = Commands.pullInputParam(callStack, amount, inputMapping, 1);
        pullTokensWithPermit(token, amount, owner, deadline, v, r, s);
        return "";
    }
    /**
     * @notice Handles the deposit to vault command.
     * @param data The encoded deposit to vault parameters.
     * @param callStack The call stack.
     * @param inputMapping The input mapping.
     * @param outputMapping The output mapping.
     * @return output The encoded output values.
     */
    function _handleVaultDeposit(
        bytes calldata data,
        uint256[] memory callStack,
        uint32 inputMapping,
        uint32 outputMapping
    ) private returns (bytes memory) {
        IERC4626 vault;
        uint256 assets;
        address receiver;
        assembly {
            vault := calldataload(data.offset)
            assets := calldataload(add(data.offset, 0x20))
            receiver := calldataload(add(data.offset, 0x40))
        }
        assets = Commands.pullInputParam(callStack, assets, inputMapping, 1);
        uint256 shares = depositVault(vault, assets, receiver);
        Commands.pushOutputParam(callStack, shares, outputMapping, 1);
        return abi.encodePacked(shares);
    }
    /**
     * @notice Handles the mint to vault command.
     * @param data The encoded mint to vault parameters.
     * @param callStack The call stack.
     * @param inputMapping The input mapping.
     * @param outputMapping The output mapping.
     * @return output The encoded output values.
     */
    function _handleVaultMint(
        bytes calldata data,
        uint256[] memory callStack,
        uint32 inputMapping,
        uint32 outputMapping
    ) private returns (bytes memory) {
        IERC4626 vault;
        uint256 shares;
        address receiver;
        assembly {
            vault := calldataload(data.offset)
            shares := calldataload(add(data.offset, 0x20))
            receiver := calldataload(add(data.offset, 0x40))
        }
        shares = Commands.pullInputParam(callStack, shares, inputMapping, 1);
        uint256 assets = mintVault(vault, shares, receiver);
        Commands.pushOutputParam(callStack, assets, outputMapping, 1);
        return abi.encodePacked(assets);
    }
    /**
     * @notice Handles the redeem from vault command.
     * @param data The encoded redeem from vault parameters.
     * @param callStack The call stack.
     * @param inputMapping The input mapping.
     * @param outputMapping The output mapping.
     * @return output The encoded output values.
     */
    function _handleVaultRedeem(
        bytes calldata data,
        uint256[] memory callStack,
        uint32 inputMapping,
        uint32 outputMapping
    ) private returns (bytes memory) {
        IERC4626 vault;
        uint256 shares;
        address receiver;
        address owner;
        assembly {
            vault := calldataload(data.offset)
            shares := calldataload(add(data.offset, 0x20))
            receiver := calldataload(add(data.offset, 0x40))
            owner := calldataload(add(data.offset, 0x60))
        }
        shares = Commands.pullInputParam(callStack, shares, inputMapping, 1);
        uint256 assets = redeemVault(vault, shares, receiver, owner);
        Commands.pushOutputParam(callStack, assets, outputMapping, 1);
        return abi.encodePacked(assets);
    }
    /**
     * @notice Handles the withdraw from vault command.
     * @param data The encoded withdraw from vault parameters.
     * @param callStack The call stack.
     * @param inputMapping The input mapping.
     * @param outputMapping The output mapping.
     * @return output The encoded output values.
     */
    function _handleVaultWithdraw(
        bytes calldata data,
        uint256[] memory callStack,
        uint32 inputMapping,
        uint32 outputMapping
    ) private returns (bytes memory) {
        IERC4626 vault;
        uint256 assets;
        address receiver;
        address owner;
        assembly {
            vault := calldataload(data.offset)
            assets := calldataload(add(data.offset, 0x20))
            receiver := calldataload(add(data.offset, 0x40))
            owner := calldataload(add(data.offset, 0x60))
        }
        assets = Commands.pullInputParam(callStack, assets, inputMapping, 1);
        uint256 shares = withdrawVault(vault, assets, receiver, owner);
        Commands.pushOutputParam(callStack, shares, outputMapping, 1);
        return abi.encodePacked(shares);
    }
    /**
     * @notice Handles the convert to shares command.
     * @param data The encoded convert to shares parameters.
     * @param callStack The call stack.
     * @param inputMapping The input mapping.
     * @param outputMapping The output mapping.
     * @return output The encoded output values.
     */
    function _handleVaultConvertToShares(
        bytes calldata data,
        uint256[] memory callStack,
        uint32 inputMapping,
        uint32 outputMapping
    ) private view returns (bytes memory) {
        IERC4626 vault;
        uint256 assets;
        assembly {
            vault := calldataload(data.offset)
            assets := calldataload(add(data.offset, 0x20))
        }
        assets = Commands.pullInputParam(callStack, assets, inputMapping, 1);
        uint256 amount = convertToVaultShares(vault, assets);
        Commands.pushOutputParam(callStack, amount, outputMapping, 1);
        return abi.encodePacked(amount);
    }
    /**
     * @notice Handles the convert to assets command.
     * @param data The encoded convert to assets parameters.
     * @param callStack The call stack.
     * @param inputMapping The input mapping.
     * @param outputMapping The output mapping.
     * @return output The encoded output values.
     */
    function _handleVaultConvertToAssets(
        bytes calldata data,
        uint256[] memory callStack,
        uint32 inputMapping,
        uint32 outputMapping
    ) private view returns (bytes memory) {
        IERC4626 vault;
        uint256 shares;
        assembly {
            vault := calldataload(data.offset)
            shares := calldataload(add(data.offset, 0x20))
        }
        shares = Commands.pullInputParam(callStack, shares, inputMapping, 1);
        uint256 amount = convertToVaultAssets(vault, shares);
        Commands.pushOutputParam(callStack, amount, outputMapping, 1);
        return abi.encodePacked(amount);
    }

    /**
     * @dev This empty reserved space is put in place to allow future versions to add new
     * variables without shifting down storage in the inheritance chain.
     */
    uint256[50] private __gap;
}

