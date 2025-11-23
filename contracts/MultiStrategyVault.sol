// SPDX-License-Identifier: BUSL-1.1
pragma solidity =0.8.24;

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

// contracts/interfaces/core/IVaultSettings.sol

/**
 * @title Bakerfi Settings Interface
 *
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 * @author Chef Kal-EL <chef.kal-el@bakerfi.xyz>
 *
 * @dev The Settings contract have to implement this interface
 *
 */
interface IVaultSettings {
    /**
     * @dev Emitted when the withdrawal fee is changed.
     *
     * This event provides information about the updated withdrawal fee.
     *
     * @param value The new withdrawal fee percentage.
     */
    event WithdrawalFeeChanged(uint256 indexed value);

    /**
     * @dev Emitted when the performance fee is changed.
     *
     * This event provides information about the updated performance fee.
     *
     * @param value The new performance fee percentage.
     */
    event PerformanceFeeChanged(uint256 indexed value);

    /**
     * @dev Emitted when the fee receiver address is changed.
     *
     * This event provides information about the updated fee receiver address.
     *
     * @param value The new fee receiver address.
     */
    event FeeReceiverChanged(address indexed value);

    /**
     * @dev Emitted when an account is added or removed from the whitelist.
     *
     * This event provides information about whether an account is enabled or disabled in the whitelist.
     *
     * @param account The address of the account affected by the whitelist change.
     * @param enabled A boolean indicating whether the account is enabled (true) or disabled (false) in the whitelist.
     */
    event AccountWhiteList(address indexed account, bool enabled);

    /**
     * @dev Emitted when the Maximum Deposit ETH is changed
     * @param value The new amount that is allowed to be deposited
     */
    event MaxDepositChanged(uint256 indexed value);
    /**
     * @dev Sets the withdrawal fee percentage.
     *     *
     * @param fee The new withdrawal fee percentage to be set.
     */
    function setWithdrawalFee(uint256 fee) external;

    /**
     * @dev Retrieves the withdrawal fee percentage.
     *
     * @return fee The withdrawal fee percentage.
     */
    function getWithdrawalFee() external view returns (uint256);
    /**
     * @dev Sets the performance fee percentage.
     *
     * @param fee The new performance fee percentage to be set.
     */
    function setPerformanceFee(uint256 fee) external;

    /**
     * @dev Retrieves the performance fee percentage.
     *
     * @return fee The performance fee percentage.
     */
    function getPerformanceFee() external view returns (uint256);
    /**
     * @dev Sets the fee receiver address.
     *
     * @param receiver The new fee receiver address to be set.
     */
    function setFeeReceiver(address receiver) external;
    /**
     * @dev Retrieves the fee receiver address.
     *
     * @return receiver The fee receiver address.
     */
    function getFeeReceiver() external view returns (address);
    /**
     * @dev Enables or disables an account in the whitelist.
     *
     * @param account The address of the account to be enabled or disabled.
     * @param enabled A boolean indicating whether the account should be enabled (true) or disabled (false) in the whitelist.
     */
    function enableAccount(address account, bool enabled) external;
    /**
     * @dev Checks if an account is enabled in the whitelist.
     *
     * @param account The address of the account to be checked.
     * @return enabled A boolean indicating whether the account is enabled (true) or not (false) in the whitelist.
     */
    function isAccountEnabled(address account) external view returns (bool);

    /**
     * @notice Retrieves the maximum deposit allowed in ETH.
     * @return The maximum deposit value in ETH.
     */
    function getMaxDeposit() external view returns (uint256);

    /**
     * @notice Sets the maximum deposit allowed in ETH.
     * @param value The maximum deposit value to be set in ETH.
     */
    function setMaxDeposit(uint256 value) external;
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

// contracts/libraries/RebaseLibrary.sol

/*
 * This library was adapted from Boring Solidity Rebase Library
 * https://github.com/boringcrypto/BoringSolidity/blob/78f4817d9c0d95fe9c45cd42e307ccd22cf5f4fc/contracts/libraries/BoringRebase.sol
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 */

struct Rebase {
    uint256 elastic;
    uint256 base;
}

/**
 * @title RebaseLibrary
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 * @dev Library for handling rebase operations. This library was adapted from Boring Solidity Rebase Library
 */
library RebaseLibrary {
    /// @notice Calculates the base value in relationship to `elastic` and `total`.
    function toBase(Rebase memory total, uint256 elastic, bool roundUp) internal pure returns (uint256 base) {
        if (total.elastic == 0 || total.base == 0) {
            base = elastic;
        } else {
            base = (elastic * total.base) / total.elastic;
            if (roundUp && (base * total.elastic) / total.base < elastic) {
                base++;
            }
        }
    }

    /// @notice Calculates the elastic value in relationship to `base` and `total`.
    function toElastic(Rebase memory total, uint256 base, bool roundUp) internal pure returns (uint256 elastic) {
        if (total.base == 0) {
            elastic = base;
        } else {
            elastic = (base * total.elastic) / total.base;
            if (roundUp && (elastic * total.base) / total.elastic < base) {
                elastic++;
            }
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

// node_modules/@openzeppelin/contracts-upgradeable/access/IAccessControlUpgradeable.sol

// OpenZeppelin Contracts v4.4.1 (access/IAccessControl.sol)

/**
 * @dev External interface of AccessControl declared to support ERC165 detection.
 */
interface IAccessControlUpgradeable {
    /**
     * @dev Emitted when `newAdminRole` is set as ``role``'s admin role, replacing `previousAdminRole`
     *
     * `DEFAULT_ADMIN_ROLE` is the starting admin for all roles, despite
     * {RoleAdminChanged} not being emitted signaling this.
     *
     * _Available since v3.1._
     */
    event RoleAdminChanged(bytes32 indexed role, bytes32 indexed previousAdminRole, bytes32 indexed newAdminRole);

    /**
     * @dev Emitted when `account` is granted `role`.
     *
     * `sender` is the account that originated the contract call, an admin role
     * bearer except when using {AccessControl-_setupRole}.
     */
    event RoleGranted(bytes32 indexed role, address indexed account, address indexed sender);

    /**
     * @dev Emitted when `account` is revoked `role`.
     *
     * `sender` is the account that originated the contract call:
     *   - if using `revokeRole`, it is the admin role bearer
     *   - if using `renounceRole`, it is the role bearer (i.e. `account`)
     */
    event RoleRevoked(bytes32 indexed role, address indexed account, address indexed sender);

    /**
     * @dev Returns `true` if `account` has been granted `role`.
     */
    function hasRole(bytes32 role, address account) external view returns (bool);

    /**
     * @dev Returns the admin role that controls `role`. See {grantRole} and
     * {revokeRole}.
     *
     * To change a role's admin, use {AccessControl-_setRoleAdmin}.
     */
    function getRoleAdmin(bytes32 role) external view returns (bytes32);

    /**
     * @dev Grants `role` to `account`.
     *
     * If `account` had not been already granted `role`, emits a {RoleGranted}
     * event.
     *
     * Requirements:
     *
     * - the caller must have ``role``'s admin role.
     */
    function grantRole(bytes32 role, address account) external;

    /**
     * @dev Revokes `role` from `account`.
     *
     * If `account` had been granted `role`, emits a {RoleRevoked} event.
     *
     * Requirements:
     *
     * - the caller must have ``role``'s admin role.
     */
    function revokeRole(bytes32 role, address account) external;

    /**
     * @dev Revokes `role` from the calling account.
     *
     * Roles are often managed via {grantRole} and {revokeRole}: this function's
     * purpose is to provide a mechanism for accounts to lose their privileges
     * if they are compromised (such as when a trusted device is misplaced).
     *
     * If the calling account had been granted `role`, emits a {RoleRevoked}
     * event.
     *
     * Requirements:
     *
     * - the caller must be `account`.
     */
    function renounceRole(bytes32 role, address account) external;
}

// node_modules/@openzeppelin/contracts-upgradeable/interfaces/IERC5267Upgradeable.sol

// OpenZeppelin Contracts (last updated v4.9.0) (interfaces/IERC5267.sol)

interface IERC5267Upgradeable {
    /**
     * @dev MAY be emitted to signal that the domain could have changed.
     */
    event EIP712DomainChanged();

    /**
     * @dev returns the fields and values that describe the domain separator used by this contract for EIP-712
     * signature.
     */
    function eip712Domain()
        external
        view
        returns (
            bytes1 fields,
            string memory name,
            string memory version,
            uint256 chainId,
            address verifyingContract,
            bytes32 salt,
            uint256[] memory extensions
        );
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

// node_modules/@openzeppelin/contracts-upgradeable/utils/CountersUpgradeable.sol

// OpenZeppelin Contracts v4.4.1 (utils/Counters.sol)

/**
 * @title Counters
 * @author Matt Condon (@shrugs)
 * @dev Provides counters that can only be incremented, decremented or reset. This can be used e.g. to track the number
 * of elements in a mapping, issuing ERC721 ids, or counting request ids.
 *
 * Include with `using Counters for Counters.Counter;`
 */
library CountersUpgradeable {
    struct Counter {
        // This variable should never be directly accessed by users of the library: interactions must be restricted to
        // the library's function. As of Solidity v0.5.2, this cannot be enforced, though there is a proposal to add
        // this feature: see https://github.com/ethereum/solidity/issues/4637
        uint256 _value; // default: 0
    }

    function current(Counter storage counter) internal view returns (uint256) {
        return counter._value;
    }

    function increment(Counter storage counter) internal {
        unchecked {
            counter._value += 1;
        }
    }

    function decrement(Counter storage counter) internal {
        uint256 value = counter._value;
        require(value > 0, "Counter: decrement overflow");
        unchecked {
            counter._value = value - 1;
        }
    }

    function reset(Counter storage counter) internal {
        counter._value = 0;
    }
}

// node_modules/@openzeppelin/contracts-upgradeable/utils/introspection/IERC165Upgradeable.sol

// OpenZeppelin Contracts v4.4.1 (utils/introspection/IERC165.sol)

/**
 * @dev Interface of the ERC165 standard, as defined in the
 * https://eips.ethereum.org/EIPS/eip-165[EIP].
 *
 * Implementers can declare support of contract interfaces, which can then be
 * queried by others ({ERC165Checker}).
 *
 * For an implementation, see {ERC165}.
 */
interface IERC165Upgradeable {
    /**
     * @dev Returns true if this contract implements the interface defined by
     * `interfaceId`. See the corresponding
     * https://eips.ethereum.org/EIPS/eip-165#how-interfaces-are-identified[EIP section]
     * to learn more about how these ids are created.
     *
     * This function call must use less than 30 000 gas.
     */
    function supportsInterface(bytes4 interfaceId) external view returns (bool);
}

// node_modules/@openzeppelin/contracts-upgradeable/utils/math/MathUpgradeable.sol

// OpenZeppelin Contracts (last updated v4.9.0) (utils/math/Math.sol)

/**
 * @dev Standard math utilities missing in the Solidity language.
 */
library MathUpgradeable {
    enum Rounding {
        Down, // Toward negative infinity
        Up, // Toward infinity
        Zero // Toward zero
    }

    /**
     * @dev Returns the largest of two numbers.
     */
    function max(uint256 a, uint256 b) internal pure returns (uint256) {
        return a > b ? a : b;
    }

    /**
     * @dev Returns the smallest of two numbers.
     */
    function min(uint256 a, uint256 b) internal pure returns (uint256) {
        return a < b ? a : b;
    }

    /**
     * @dev Returns the average of two numbers. The result is rounded towards
     * zero.
     */
    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b) / 2 can overflow.
        return (a & b) + (a ^ b) / 2;
    }

    /**
     * @dev Returns the ceiling of the division of two numbers.
     *
     * This differs from standard division with `/` in that it rounds up instead
     * of rounding down.
     */
    function ceilDiv(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b - 1) / b can overflow on addition, so we distribute.
        return a == 0 ? 0 : (a - 1) / b + 1;
    }

    /**
     * @notice Calculates floor(x * y / denominator) with full precision. Throws if result overflows a uint256 or denominator == 0
     * @dev Original credit to Remco Bloemen under MIT license (https://xn--2-umb.com/21/muldiv)
     * with further edits by Uniswap Labs also under MIT license.
     */
    function mulDiv(uint256 x, uint256 y, uint256 denominator) internal pure returns (uint256 result) {
        unchecked {
            // 512-bit multiply [prod1 prod0] = x * y. Compute the product mod 2^256 and mod 2^256 - 1, then use
            // use the Chinese Remainder Theorem to reconstruct the 512 bit result. The result is stored in two 256
            // variables such that product = prod1 * 2^256 + prod0.
            uint256 prod0; // Least significant 256 bits of the product
            uint256 prod1; // Most significant 256 bits of the product
            assembly {
                let mm := mulmod(x, y, not(0))
                prod0 := mul(x, y)
                prod1 := sub(sub(mm, prod0), lt(mm, prod0))
            }

            // Handle non-overflow cases, 256 by 256 division.
            if (prod1 == 0) {
                // Solidity will revert if denominator == 0, unlike the div opcode on its own.
                // The surrounding unchecked block does not change this fact.
                // See https://docs.soliditylang.org/en/latest/control-structures.html#checked-or-unchecked-arithmetic.
                return prod0 / denominator;
            }

            // Make sure the result is less than 2^256. Also prevents denominator == 0.
            require(denominator > prod1, "Math: mulDiv overflow");

            ///////////////////////////////////////////////
            // 512 by 256 division.
            ///////////////////////////////////////////////

            // Make division exact by subtracting the remainder from [prod1 prod0].
            uint256 remainder;
            assembly {
                // Compute remainder using mulmod.
                remainder := mulmod(x, y, denominator)

                // Subtract 256 bit number from 512 bit number.
                prod1 := sub(prod1, gt(remainder, prod0))
                prod0 := sub(prod0, remainder)
            }

            // Factor powers of two out of denominator and compute largest power of two divisor of denominator. Always >= 1.
            // See https://cs.stackexchange.com/q/138556/92363.

            // Does not overflow because the denominator cannot be zero at this stage in the function.
            uint256 twos = denominator & (~denominator + 1);
            assembly {
                // Divide denominator by twos.
                denominator := div(denominator, twos)

                // Divide [prod1 prod0] by twos.
                prod0 := div(prod0, twos)

                // Flip twos such that it is 2^256 / twos. If twos is zero, then it becomes one.
                twos := add(div(sub(0, twos), twos), 1)
            }

            // Shift in bits from prod1 into prod0.
            prod0 |= prod1 * twos;

            // Invert denominator mod 2^256. Now that denominator is an odd number, it has an inverse modulo 2^256 such
            // that denominator * inv = 1 mod 2^256. Compute the inverse by starting with a seed that is correct for
            // four bits. That is, denominator * inv = 1 mod 2^4.
            uint256 inverse = (3 * denominator) ^ 2;

            // Use the Newton-Raphson iteration to improve the precision. Thanks to Hensel's lifting lemma, this also works
            // in modular arithmetic, doubling the correct bits in each step.
            inverse *= 2 - denominator * inverse; // inverse mod 2^8
            inverse *= 2 - denominator * inverse; // inverse mod 2^16
            inverse *= 2 - denominator * inverse; // inverse mod 2^32
            inverse *= 2 - denominator * inverse; // inverse mod 2^64
            inverse *= 2 - denominator * inverse; // inverse mod 2^128
            inverse *= 2 - denominator * inverse; // inverse mod 2^256

            // Because the division is now exact we can divide by multiplying with the modular inverse of denominator.
            // This will give us the correct result modulo 2^256. Since the preconditions guarantee that the outcome is
            // less than 2^256, this is the final result. We don't need to compute the high bits of the result and prod1
            // is no longer required.
            result = prod0 * inverse;
            return result;
        }
    }

    /**
     * @notice Calculates x * y / denominator with full precision, following the selected rounding direction.
     */
    function mulDiv(uint256 x, uint256 y, uint256 denominator, Rounding rounding) internal pure returns (uint256) {
        uint256 result = mulDiv(x, y, denominator);
        if (rounding == Rounding.Up && mulmod(x, y, denominator) > 0) {
            result += 1;
        }
        return result;
    }

    /**
     * @dev Returns the square root of a number. If the number is not a perfect square, the value is rounded down.
     *
     * Inspired by Henry S. Warren, Jr.'s "Hacker's Delight" (Chapter 11).
     */
    function sqrt(uint256 a) internal pure returns (uint256) {
        if (a == 0) {
            return 0;
        }

        // For our first guess, we get the biggest power of 2 which is smaller than the square root of the target.
        //
        // We know that the "msb" (most significant bit) of our target number `a` is a power of 2 such that we have
        // `msb(a) <= a < 2*msb(a)`. This value can be written `msb(a)=2**k` with `k=log2(a)`.
        //
        // This can be rewritten `2**log2(a) <= a < 2**(log2(a) + 1)`
        // → `sqrt(2**k) <= sqrt(a) < sqrt(2**(k+1))`
        // → `2**(k/2) <= sqrt(a) < 2**((k+1)/2) <= 2**(k/2 + 1)`
        //
        // Consequently, `2**(log2(a) / 2)` is a good first approximation of `sqrt(a)` with at least 1 correct bit.
        uint256 result = 1 << (log2(a) >> 1);

        // At this point `result` is an estimation with one bit of precision. We know the true value is a uint128,
        // since it is the square root of a uint256. Newton's method converges quadratically (precision doubles at
        // every iteration). We thus need at most 7 iteration to turn our partial result with one bit of precision
        // into the expected uint128 result.
        unchecked {
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            return min(result, a / result);
        }
    }

    /**
     * @notice Calculates sqrt(a), following the selected rounding direction.
     */
    function sqrt(uint256 a, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = sqrt(a);
            return result + (rounding == Rounding.Up && result * result < a ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 2, rounded down, of a positive value.
     * Returns 0 if given 0.
     */
    function log2(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >> 128 > 0) {
                value >>= 128;
                result += 128;
            }
            if (value >> 64 > 0) {
                value >>= 64;
                result += 64;
            }
            if (value >> 32 > 0) {
                value >>= 32;
                result += 32;
            }
            if (value >> 16 > 0) {
                value >>= 16;
                result += 16;
            }
            if (value >> 8 > 0) {
                value >>= 8;
                result += 8;
            }
            if (value >> 4 > 0) {
                value >>= 4;
                result += 4;
            }
            if (value >> 2 > 0) {
                value >>= 2;
                result += 2;
            }
            if (value >> 1 > 0) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 2, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log2(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log2(value);
            return result + (rounding == Rounding.Up && 1 << result < value ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 10, rounded down, of a positive value.
     * Returns 0 if given 0.
     */
    function log10(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >= 10 ** 64) {
                value /= 10 ** 64;
                result += 64;
            }
            if (value >= 10 ** 32) {
                value /= 10 ** 32;
                result += 32;
            }
            if (value >= 10 ** 16) {
                value /= 10 ** 16;
                result += 16;
            }
            if (value >= 10 ** 8) {
                value /= 10 ** 8;
                result += 8;
            }
            if (value >= 10 ** 4) {
                value /= 10 ** 4;
                result += 4;
            }
            if (value >= 10 ** 2) {
                value /= 10 ** 2;
                result += 2;
            }
            if (value >= 10 ** 1) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 10, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log10(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log10(value);
            return result + (rounding == Rounding.Up && 10 ** result < value ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 256, rounded down, of a positive value.
     * Returns 0 if given 0.
     *
     * Adding one to the result gives the number of pairs of hex symbols needed to represent `value` as a hex string.
     */
    function log256(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >> 128 > 0) {
                value >>= 128;
                result += 16;
            }
            if (value >> 64 > 0) {
                value >>= 64;
                result += 8;
            }
            if (value >> 32 > 0) {
                value >>= 32;
                result += 4;
            }
            if (value >> 16 > 0) {
                value >>= 16;
                result += 2;
            }
            if (value >> 8 > 0) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 256, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log256(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log256(value);
            return result + (rounding == Rounding.Up && 1 << (result << 3) < value ? 1 : 0);
        }
    }
}

// node_modules/@openzeppelin/contracts-upgradeable/utils/math/SignedMathUpgradeable.sol

// OpenZeppelin Contracts (last updated v4.8.0) (utils/math/SignedMath.sol)

/**
 * @dev Standard signed math utilities missing in the Solidity language.
 */
library SignedMathUpgradeable {
    /**
     * @dev Returns the largest of two signed numbers.
     */
    function max(int256 a, int256 b) internal pure returns (int256) {
        return a > b ? a : b;
    }

    /**
     * @dev Returns the smallest of two signed numbers.
     */
    function min(int256 a, int256 b) internal pure returns (int256) {
        return a < b ? a : b;
    }

    /**
     * @dev Returns the average of two signed numbers without overflow.
     * The result is rounded towards zero.
     */
    function average(int256 a, int256 b) internal pure returns (int256) {
        // Formula from the book "Hacker's Delight"
        int256 x = (a & b) + ((a ^ b) >> 1);
        return x + (int256(uint256(x) >> 255) & (a ^ b));
    }

    /**
     * @dev Returns the absolute unsigned value of a signed value.
     */
    function abs(int256 n) internal pure returns (uint256) {
        unchecked {
            // must be unchecked in order to support `n = type(int256).min`
            return uint256(n >= 0 ? n : -n);
        }
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

// node_modules/@openzeppelin/contracts-upgradeable/interfaces/IERC20Upgradeable.sol

// OpenZeppelin Contracts v4.4.1 (interfaces/IERC20.sol)

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

// node_modules/@openzeppelin/contracts-upgradeable/token/ERC20/extensions/IERC20MetadataUpgradeable.sol

// OpenZeppelin Contracts v4.4.1 (token/ERC20/extensions/IERC20Metadata.sol)

/**
 * @dev Interface for the optional metadata functions from the ERC20 standard.
 *
 * _Available since v4.1._
 */
interface IERC20MetadataUpgradeable is IERC20Upgradeable {
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

// node_modules/@openzeppelin/contracts-upgradeable/interfaces/IERC4626Upgradeable.sol

// OpenZeppelin Contracts (last updated v4.9.0) (interfaces/IERC4626.sol)

/**
 * @dev Interface of the ERC4626 "Tokenized Vault Standard", as defined in
 * https://eips.ethereum.org/EIPS/eip-4626[ERC-4626].
 *
 * _Available since v4.7._
 */
interface IERC4626Upgradeable is IERC20Upgradeable, IERC20MetadataUpgradeable {
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

// node_modules/@openzeppelin/contracts-upgradeable/utils/StringsUpgradeable.sol

// OpenZeppelin Contracts (last updated v4.9.0) (utils/Strings.sol)

/**
 * @dev String operations.
 */
library StringsUpgradeable {
    bytes16 private constant _SYMBOLS = "0123456789abcdef";
    uint8 private constant _ADDRESS_LENGTH = 20;

    /**
     * @dev Converts a `uint256` to its ASCII `string` decimal representation.
     */
    function toString(uint256 value) internal pure returns (string memory) {
        unchecked {
            uint256 length = MathUpgradeable.log10(value) + 1;
            string memory buffer = new string(length);
            uint256 ptr;
            /// @solidity memory-safe-assembly
            assembly {
                ptr := add(buffer, add(32, length))
            }
            while (true) {
                ptr--;
                /// @solidity memory-safe-assembly
                assembly {
                    mstore8(ptr, byte(mod(value, 10), _SYMBOLS))
                }
                value /= 10;
                if (value == 0) break;
            }
            return buffer;
        }
    }

    /**
     * @dev Converts a `int256` to its ASCII `string` decimal representation.
     */
    function toString(int256 value) internal pure returns (string memory) {
        return string(abi.encodePacked(value < 0 ? "-" : "", toString(SignedMathUpgradeable.abs(value))));
    }

    /**
     * @dev Converts a `uint256` to its ASCII `string` hexadecimal representation.
     */
    function toHexString(uint256 value) internal pure returns (string memory) {
        unchecked {
            return toHexString(value, MathUpgradeable.log256(value) + 1);
        }
    }

    /**
     * @dev Converts a `uint256` to its ASCII `string` hexadecimal representation with fixed length.
     */
    function toHexString(uint256 value, uint256 length) internal pure returns (string memory) {
        bytes memory buffer = new bytes(2 * length + 2);
        buffer[0] = "0";
        buffer[1] = "x";
        for (uint256 i = 2 * length + 1; i > 1; --i) {
            buffer[i] = _SYMBOLS[value & 0xf];
            value >>= 4;
        }
        require(value == 0, "Strings: hex length insufficient");
        return string(buffer);
    }

    /**
     * @dev Converts an `address` with fixed length of 20 bytes to its not checksummed ASCII `string` hexadecimal representation.
     */
    function toHexString(address addr) internal pure returns (string memory) {
        return toHexString(uint256(uint160(addr)), _ADDRESS_LENGTH);
    }

    /**
     * @dev Returns true if the two strings are equal.
     */
    function equal(string memory a, string memory b) internal pure returns (bool) {
        return keccak256(bytes(a)) == keccak256(bytes(b));
    }
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

// node_modules/@openzeppelin/contracts-upgradeable/security/PausableUpgradeable.sol

// OpenZeppelin Contracts (last updated v4.7.0) (security/Pausable.sol)

/**
 * @dev Contract module which allows children to implement an emergency stop
 * mechanism that can be triggered by an authorized account.
 *
 * This module is used through inheritance. It will make available the
 * modifiers `whenNotPaused` and `whenPaused`, which can be applied to
 * the functions of your contract. Note that they will not be pausable by
 * simply including this module, only once the modifiers are put in place.
 */
abstract contract PausableUpgradeable is Initializable, ContextUpgradeable {
    /**
     * @dev Emitted when the pause is triggered by `account`.
     */
    event Paused(address account);

    /**
     * @dev Emitted when the pause is lifted by `account`.
     */
    event Unpaused(address account);

    bool private _paused;

    /**
     * @dev Initializes the contract in unpaused state.
     */
    function __Pausable_init() internal onlyInitializing {
        __Pausable_init_unchained();
    }

    function __Pausable_init_unchained() internal onlyInitializing {
        _paused = false;
    }

    /**
     * @dev Modifier to make a function callable only when the contract is not paused.
     *
     * Requirements:
     *
     * - The contract must not be paused.
     */
    modifier whenNotPaused() {
        _requireNotPaused();
        _;
    }

    /**
     * @dev Modifier to make a function callable only when the contract is paused.
     *
     * Requirements:
     *
     * - The contract must be paused.
     */
    modifier whenPaused() {
        _requirePaused();
        _;
    }

    /**
     * @dev Returns true if the contract is paused, and false otherwise.
     */
    function paused() public view virtual returns (bool) {
        return _paused;
    }

    /**
     * @dev Throws if the contract is paused.
     */
    function _requireNotPaused() internal view virtual {
        require(!paused(), "Pausable: paused");
    }

    /**
     * @dev Throws if the contract is not paused.
     */
    function _requirePaused() internal view virtual {
        require(paused(), "Pausable: not paused");
    }

    /**
     * @dev Triggers stopped state.
     *
     * Requirements:
     *
     * - The contract must not be paused.
     */
    function _pause() internal virtual whenNotPaused {
        _paused = true;
        emit Paused(_msgSender());
    }

    /**
     * @dev Returns to normal state.
     *
     * Requirements:
     *
     * - The contract must be paused.
     */
    function _unpause() internal virtual whenPaused {
        _paused = false;
        emit Unpaused(_msgSender());
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

// node_modules/@openzeppelin/contracts-upgradeable/utils/cryptography/ECDSAUpgradeable.sol

// OpenZeppelin Contracts (last updated v4.9.0) (utils/cryptography/ECDSA.sol)

/**
 * @dev Elliptic Curve Digital Signature Algorithm (ECDSA) operations.
 *
 * These functions can be used to verify that a message was signed by the holder
 * of the private keys of a given address.
 */
library ECDSAUpgradeable {
    enum RecoverError {
        NoError,
        InvalidSignature,
        InvalidSignatureLength,
        InvalidSignatureS,
        InvalidSignatureV // Deprecated in v4.8
    }

    function _throwError(RecoverError error) private pure {
        if (error == RecoverError.NoError) {
            return; // no error: do nothing
        } else if (error == RecoverError.InvalidSignature) {
            revert("ECDSA: invalid signature");
        } else if (error == RecoverError.InvalidSignatureLength) {
            revert("ECDSA: invalid signature length");
        } else if (error == RecoverError.InvalidSignatureS) {
            revert("ECDSA: invalid signature 's' value");
        }
    }

    /**
     * @dev Returns the address that signed a hashed message (`hash`) with
     * `signature` or error string. This address can then be used for verification purposes.
     *
     * The `ecrecover` EVM opcode allows for malleable (non-unique) signatures:
     * this function rejects them by requiring the `s` value to be in the lower
     * half order, and the `v` value to be either 27 or 28.
     *
     * IMPORTANT: `hash` _must_ be the result of a hash operation for the
     * verification to be secure: it is possible to craft signatures that
     * recover to arbitrary addresses for non-hashed data. A safe way to ensure
     * this is by receiving a hash of the original message (which may otherwise
     * be too long), and then calling {toEthSignedMessageHash} on it.
     *
     * Documentation for signature generation:
     * - with https://web3js.readthedocs.io/en/v1.3.4/web3-eth-accounts.html#sign[Web3.js]
     * - with https://docs.ethers.io/v5/api/signer/#Signer-signMessage[ethers]
     *
     * _Available since v4.3._
     */
    function tryRecover(bytes32 hash, bytes memory signature) internal pure returns (address, RecoverError) {
        if (signature.length == 65) {
            bytes32 r;
            bytes32 s;
            uint8 v;
            // ecrecover takes the signature parameters, and the only way to get them
            // currently is to use assembly.
            /// @solidity memory-safe-assembly
            assembly {
                r := mload(add(signature, 0x20))
                s := mload(add(signature, 0x40))
                v := byte(0, mload(add(signature, 0x60)))
            }
            return tryRecover(hash, v, r, s);
        } else {
            return (address(0), RecoverError.InvalidSignatureLength);
        }
    }

    /**
     * @dev Returns the address that signed a hashed message (`hash`) with
     * `signature`. This address can then be used for verification purposes.
     *
     * The `ecrecover` EVM opcode allows for malleable (non-unique) signatures:
     * this function rejects them by requiring the `s` value to be in the lower
     * half order, and the `v` value to be either 27 or 28.
     *
     * IMPORTANT: `hash` _must_ be the result of a hash operation for the
     * verification to be secure: it is possible to craft signatures that
     * recover to arbitrary addresses for non-hashed data. A safe way to ensure
     * this is by receiving a hash of the original message (which may otherwise
     * be too long), and then calling {toEthSignedMessageHash} on it.
     */
    function recover(bytes32 hash, bytes memory signature) internal pure returns (address) {
        (address recovered, RecoverError error) = tryRecover(hash, signature);
        _throwError(error);
        return recovered;
    }

    /**
     * @dev Overload of {ECDSA-tryRecover} that receives the `r` and `vs` short-signature fields separately.
     *
     * See https://eips.ethereum.org/EIPS/eip-2098[EIP-2098 short signatures]
     *
     * _Available since v4.3._
     */
    function tryRecover(bytes32 hash, bytes32 r, bytes32 vs) internal pure returns (address, RecoverError) {
        bytes32 s = vs & bytes32(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
        uint8 v = uint8((uint256(vs) >> 255) + 27);
        return tryRecover(hash, v, r, s);
    }

    /**
     * @dev Overload of {ECDSA-recover} that receives the `r and `vs` short-signature fields separately.
     *
     * _Available since v4.2._
     */
    function recover(bytes32 hash, bytes32 r, bytes32 vs) internal pure returns (address) {
        (address recovered, RecoverError error) = tryRecover(hash, r, vs);
        _throwError(error);
        return recovered;
    }

    /**
     * @dev Overload of {ECDSA-tryRecover} that receives the `v`,
     * `r` and `s` signature fields separately.
     *
     * _Available since v4.3._
     */
    function tryRecover(bytes32 hash, uint8 v, bytes32 r, bytes32 s) internal pure returns (address, RecoverError) {
        // EIP-2 still allows signature malleability for ecrecover(). Remove this possibility and make the signature
        // unique. Appendix F in the Ethereum Yellow paper (https://ethereum.github.io/yellowpaper/paper.pdf), defines
        // the valid range for s in (301): 0 < s < secp256k1n ÷ 2 + 1, and for v in (302): v ∈ {27, 28}. Most
        // signatures from current libraries generate a unique signature with an s-value in the lower half order.
        //
        // If your library generates malleable signatures, such as s-values in the upper range, calculate a new s-value
        // with 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141 - s1 and flip v from 27 to 28 or
        // vice versa. If your library also generates signatures with 0/1 for v instead 27/28, add 27 to v to accept
        // these malleable signatures as well.
        if (uint256(s) > 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0) {
            return (address(0), RecoverError.InvalidSignatureS);
        }

        // If the signature is valid (and not malleable), return the signer address
        address signer = ecrecover(hash, v, r, s);
        if (signer == address(0)) {
            return (address(0), RecoverError.InvalidSignature);
        }

        return (signer, RecoverError.NoError);
    }

    /**
     * @dev Overload of {ECDSA-recover} that receives the `v`,
     * `r` and `s` signature fields separately.
     */
    function recover(bytes32 hash, uint8 v, bytes32 r, bytes32 s) internal pure returns (address) {
        (address recovered, RecoverError error) = tryRecover(hash, v, r, s);
        _throwError(error);
        return recovered;
    }

    /**
     * @dev Returns an Ethereum Signed Message, created from a `hash`. This
     * produces hash corresponding to the one signed with the
     * https://eth.wiki/json-rpc/API#eth_sign[`eth_sign`]
     * JSON-RPC method as part of EIP-191.
     *
     * See {recover}.
     */
    function toEthSignedMessageHash(bytes32 hash) internal pure returns (bytes32 message) {
        // 32 is the length in bytes of hash,
        // enforced by the type signature above
        /// @solidity memory-safe-assembly
        assembly {
            mstore(0x00, "\x19Ethereum Signed Message:\n32")
            mstore(0x1c, hash)
            message := keccak256(0x00, 0x3c)
        }
    }

    /**
     * @dev Returns an Ethereum Signed Message, created from `s`. This
     * produces hash corresponding to the one signed with the
     * https://eth.wiki/json-rpc/API#eth_sign[`eth_sign`]
     * JSON-RPC method as part of EIP-191.
     *
     * See {recover}.
     */
    function toEthSignedMessageHash(bytes memory s) internal pure returns (bytes32) {
        return keccak256(abi.encodePacked("\x19Ethereum Signed Message:\n", StringsUpgradeable.toString(s.length), s));
    }

    /**
     * @dev Returns an Ethereum Signed Typed Data, created from a
     * `domainSeparator` and a `structHash`. This produces hash corresponding
     * to the one signed with the
     * https://eips.ethereum.org/EIPS/eip-712[`eth_signTypedData`]
     * JSON-RPC method as part of EIP-712.
     *
     * See {recover}.
     */
    function toTypedDataHash(bytes32 domainSeparator, bytes32 structHash) internal pure returns (bytes32 data) {
        /// @solidity memory-safe-assembly
        assembly {
            let ptr := mload(0x40)
            mstore(ptr, "\x19\x01")
            mstore(add(ptr, 0x02), domainSeparator)
            mstore(add(ptr, 0x22), structHash)
            data := keccak256(ptr, 0x42)
        }
    }

    /**
     * @dev Returns an Ethereum Signed Data with intended validator, created from a
     * `validator` and `data` according to the version 0 of EIP-191.
     *
     * See {recover}.
     */
    function toDataWithIntendedValidatorHash(address validator, bytes memory data) internal pure returns (bytes32) {
        return keccak256(abi.encodePacked("\x19\x00", validator, data));
    }
}

// node_modules/@openzeppelin/contracts-upgradeable/utils/introspection/ERC165Upgradeable.sol

// OpenZeppelin Contracts v4.4.1 (utils/introspection/ERC165.sol)

/**
 * @dev Implementation of the {IERC165} interface.
 *
 * Contracts that want to implement ERC165 should inherit from this contract and override {supportsInterface} to check
 * for the additional interface id that will be supported. For example:
 *
 * ```solidity
 * function supportsInterface(bytes4 interfaceId) public view virtual override returns (bool) {
 *     return interfaceId == type(MyInterface).interfaceId || super.supportsInterface(interfaceId);
 * }
 * ```
 *
 * Alternatively, {ERC165Storage} provides an easier to use but more expensive implementation.
 */
abstract contract ERC165Upgradeable is Initializable, IERC165Upgradeable {
    function __ERC165_init() internal onlyInitializing {
    }

    function __ERC165_init_unchained() internal onlyInitializing {
    }
    /**
     * @dev See {IERC165-supportsInterface}.
     */
    function supportsInterface(bytes4 interfaceId) public view virtual override returns (bool) {
        return interfaceId == type(IERC165Upgradeable).interfaceId;
    }

    /**
     * @dev This empty reserved space is put in place to allow future versions to add new
     * variables without shifting down storage in the inheritance chain.
     * See https://docs.openzeppelin.com/contracts/4.x/upgradeable#storage_gaps
     */
    uint256[50] private __gap;
}

// contracts/interfaces/core/IVault.sol

/**
 * @title BakerFi IVault 🏦🧑‍🍳
 *
 * This vault class follows the ERC4626 standard and allows the support native
 * currencies like ETHEREUM.
 *
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 * @author Chef Kal-EL <chef.kal-el@bakerfi.xyz>
 *
 * */
interface IVault is IERC20Upgradeable, IERC20MetadataUpgradeable, IERC4626Upgradeable {
    struct RebalanceCommand {
        uint256 action;
        bytes data;
    }
    /**
     * Deposits ETH or the native currency on the strategy
     *
     * The strategy should support ETH as the deployed asset
     *
     * @param receiver Receiver of the minted shares after deposit
     */
    function depositNative(address receiver) external payable returns (uint256 shares);

    /**
     * @dev Reedemns ETH or the native currency from the strategy
     *
     * The strategy should support ETH as the deployed asset
     *
     * @param assets Receiver of the minted shares after deposit
     */
    function withdrawNative(uint256 assets) external returns (uint256 shares);

    /**
     * @dev Reedemns ETH or the native currency from the strategy
     *
     * The strategy should support ETH as the deployed asset
     *
     * @param shares Receiver of the minted shares after deposit
     */

    function redeemNative(uint256 shares) external returns (uint256 assets);

    /**
     * @dev The Vault Ration between the token price and the shares
     * price. It could be used as price oracle for external entities
     *
     */
    function tokenPerAsset() external view returns (uint256 rate);

    /**
     * @dev Function to rebalance the strategy, prevent a liquidation and pay fees
     * to protocol by minting shares to the fee receiver
     *
     * @param commands The data to be passed to the rebalance function
     * @return success The success of the rebalance operation.
     *
     */
    function rebalance(RebalanceCommand[] calldata commands) external returns (bool success);
}

// node_modules/@openzeppelin/contracts-upgradeable/token/ERC20/ERC20Upgradeable.sol

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
contract ERC20Upgradeable is Initializable, ContextUpgradeable, IERC20Upgradeable, IERC20MetadataUpgradeable {
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
    function __ERC20_init(string memory name_, string memory symbol_) internal onlyInitializing {
        __ERC20_init_unchained(name_, symbol_);
    }

    function __ERC20_init_unchained(string memory name_, string memory symbol_) internal onlyInitializing {
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

    /**
     * @dev This empty reserved space is put in place to allow future versions to add new
     * variables without shifting down storage in the inheritance chain.
     * See https://docs.openzeppelin.com/contracts/4.x/upgradeable#storage_gaps
     */
    uint256[45] private __gap;
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



// node_modules/@openzeppelin/contracts-upgradeable/utils/cryptography/EIP712Upgradeable.sol

// OpenZeppelin Contracts (last updated v4.9.0) (utils/cryptography/EIP712.sol)

/**
 * @dev https://eips.ethereum.org/EIPS/eip-712[EIP 712] is a standard for hashing and signing of typed structured data.
 *
 * The encoding specified in the EIP is very generic, and such a generic implementation in Solidity is not feasible,
 * thus this contract does not implement the encoding itself. Protocols need to implement the type-specific encoding
 * they need in their contracts using a combination of `abi.encode` and `keccak256`.
 *
 * This contract implements the EIP 712 domain separator ({_domainSeparatorV4}) that is used as part of the encoding
 * scheme, and the final step of the encoding to obtain the message digest that is then signed via ECDSA
 * ({_hashTypedDataV4}).
 *
 * The implementation of the domain separator was designed to be as efficient as possible while still properly updating
 * the chain id to protect against replay attacks on an eventual fork of the chain.
 *
 * NOTE: This contract implements the version of the encoding known as "v4", as implemented by the JSON RPC method
 * https://docs.metamask.io/guide/signing-data.html[`eth_signTypedDataV4` in MetaMask].
 *
 * NOTE: In the upgradeable version of this contract, the cached values will correspond to the address, and the domain
 * separator of the implementation contract. This will cause the `_domainSeparatorV4` function to always rebuild the
 * separator from the immutable values, which is cheaper than accessing a cached version in cold storage.
 *
 * _Available since v3.4._
 *
 * @custom:storage-size 52
 */
abstract contract EIP712Upgradeable is Initializable, IERC5267Upgradeable {
    bytes32 private constant _TYPE_HASH =
        keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)");

    /// @custom:oz-renamed-from _HASHED_NAME
    bytes32 private _hashedName;
    /// @custom:oz-renamed-from _HASHED_VERSION
    bytes32 private _hashedVersion;

    string private _name;
    string private _version;

    /**
     * @dev Initializes the domain separator and parameter caches.
     *
     * The meaning of `name` and `version` is specified in
     * https://eips.ethereum.org/EIPS/eip-712#definition-of-domainseparator[EIP 712]:
     *
     * - `name`: the user readable name of the signing domain, i.e. the name of the DApp or the protocol.
     * - `version`: the current major version of the signing domain.
     *
     * NOTE: These parameters cannot be changed except through a xref:learn::upgrading-smart-contracts.adoc[smart
     * contract upgrade].
     */
    function __EIP712_init(string memory name, string memory version) internal onlyInitializing {
        __EIP712_init_unchained(name, version);
    }

    function __EIP712_init_unchained(string memory name, string memory version) internal onlyInitializing {
        _name = name;
        _version = version;

        // Reset prior values in storage if upgrading
        _hashedName = 0;
        _hashedVersion = 0;
    }

    /**
     * @dev Returns the domain separator for the current chain.
     */
    function _domainSeparatorV4() internal view returns (bytes32) {
        return _buildDomainSeparator();
    }

    function _buildDomainSeparator() private view returns (bytes32) {
        return keccak256(abi.encode(_TYPE_HASH, _EIP712NameHash(), _EIP712VersionHash(), block.chainid, address(this)));
    }

    /**
     * @dev Given an already https://eips.ethereum.org/EIPS/eip-712#definition-of-hashstruct[hashed struct], this
     * function returns the hash of the fully encoded EIP712 message for this domain.
     *
     * This hash can be used together with {ECDSA-recover} to obtain the signer of a message. For example:
     *
     * ```solidity
     * bytes32 digest = _hashTypedDataV4(keccak256(abi.encode(
     *     keccak256("Mail(address to,string contents)"),
     *     mailTo,
     *     keccak256(bytes(mailContents))
     * )));
     * address signer = ECDSA.recover(digest, signature);
     * ```
     */
    function _hashTypedDataV4(bytes32 structHash) internal view virtual returns (bytes32) {
        return ECDSAUpgradeable.toTypedDataHash(_domainSeparatorV4(), structHash);
    }

    /**
     * @dev See {EIP-5267}.
     *
     * _Available since v4.9._
     */
    function eip712Domain()
        public
        view
        virtual
        override
        returns (
            bytes1 fields,
            string memory name,
            string memory version,
            uint256 chainId,
            address verifyingContract,
            bytes32 salt,
            uint256[] memory extensions
        )
    {
        // If the hashed name and version in storage are non-zero, the contract hasn't been properly initialized
        // and the EIP712 domain is not reliable, as it will be missing name and version.
        require(_hashedName == 0 && _hashedVersion == 0, "EIP712: Uninitialized");

        return (
            hex"0f", // 01111
            _EIP712Name(),
            _EIP712Version(),
            block.chainid,
            address(this),
            bytes32(0),
            new uint256[](0)
        );
    }

    /**
     * @dev The name parameter for the EIP712 domain.
     *
     * NOTE: This function reads from storage by default, but can be redefined to return a constant value if gas costs
     * are a concern.
     */
    function _EIP712Name() internal virtual view returns (string memory) {
        return _name;
    }

    /**
     * @dev The version parameter for the EIP712 domain.
     *
     * NOTE: This function reads from storage by default, but can be redefined to return a constant value if gas costs
     * are a concern.
     */
    function _EIP712Version() internal virtual view returns (string memory) {
        return _version;
    }

    /**
     * @dev The hash of the name parameter for the EIP712 domain.
     *
     * NOTE: In previous versions this function was virtual. In this version you should override `_EIP712Name` instead.
     */
    function _EIP712NameHash() internal view returns (bytes32) {
        string memory name = _EIP712Name();
        if (bytes(name).length > 0) {
            return keccak256(bytes(name));
        } else {
            // If the name is empty, the contract may have been upgraded without initializing the new storage.
            // We return the name hash in storage if non-zero, otherwise we assume the name is empty by design.
            bytes32 hashedName = _hashedName;
            if (hashedName != 0) {
                return hashedName;
            } else {
                return keccak256("");
            }
        }
    }

    /**
     * @dev The hash of the version parameter for the EIP712 domain.
     *
     * NOTE: In previous versions this function was virtual. In this version you should override `_EIP712Version` instead.
     */
    function _EIP712VersionHash() internal view returns (bytes32) {
        string memory version = _EIP712Version();
        if (bytes(version).length > 0) {
            return keccak256(bytes(version));
        } else {
            // If the version is empty, the contract may have been upgraded without initializing the new storage.
            // We return the version hash in storage if non-zero, otherwise we assume the version is empty by design.
            bytes32 hashedVersion = _hashedVersion;
            if (hashedVersion != 0) {
                return hashedVersion;
            } else {
                return keccak256("");
            }
        }
    }

    /**
     * @dev This empty reserved space is put in place to allow future versions to add new
     * variables without shifting down storage in the inheritance chain.
     * See https://docs.openzeppelin.com/contracts/4.x/upgradeable#storage_gaps
     */
    uint256[48] private __gap;
}

// node_modules/@openzeppelin/contracts-upgradeable/access/AccessControlUpgradeable.sol

// OpenZeppelin Contracts (last updated v4.9.0) (access/AccessControl.sol)

/**
 * @dev Contract module that allows children to implement role-based access
 * control mechanisms. This is a lightweight version that doesn't allow enumerating role
 * members except through off-chain means by accessing the contract event logs. Some
 * applications may benefit from on-chain enumerability, for those cases see
 * {AccessControlEnumerable}.
 *
 * Roles are referred to by their `bytes32` identifier. These should be exposed
 * in the external API and be unique. The best way to achieve this is by
 * using `public constant` hash digests:
 *
 * ```solidity
 * bytes32 public constant MY_ROLE = keccak256("MY_ROLE");
 * ```
 *
 * Roles can be used to represent a set of permissions. To restrict access to a
 * function call, use {hasRole}:
 *
 * ```solidity
 * function foo() public {
 *     require(hasRole(MY_ROLE, msg.sender));
 *     ...
 * }
 * ```
 *
 * Roles can be granted and revoked dynamically via the {grantRole} and
 * {revokeRole} functions. Each role has an associated admin role, and only
 * accounts that have a role's admin role can call {grantRole} and {revokeRole}.
 *
 * By default, the admin role for all roles is `DEFAULT_ADMIN_ROLE`, which means
 * that only accounts with this role will be able to grant or revoke other
 * roles. More complex role relationships can be created by using
 * {_setRoleAdmin}.
 *
 * WARNING: The `DEFAULT_ADMIN_ROLE` is also its own admin: it has permission to
 * grant and revoke this role. Extra precautions should be taken to secure
 * accounts that have been granted it. We recommend using {AccessControlDefaultAdminRules}
 * to enforce additional security measures for this role.
 */
abstract contract AccessControlUpgradeable is Initializable, ContextUpgradeable, IAccessControlUpgradeable, ERC165Upgradeable {
    struct RoleData {
        mapping(address => bool) members;
        bytes32 adminRole;
    }

    mapping(bytes32 => RoleData) private _roles;

    bytes32 public constant DEFAULT_ADMIN_ROLE = 0x00;

    /**
     * @dev Modifier that checks that an account has a specific role. Reverts
     * with a standardized message including the required role.
     *
     * The format of the revert reason is given by the following regular expression:
     *
     *  /^AccessControl: account (0x[0-9a-f]{40}) is missing role (0x[0-9a-f]{64})$/
     *
     * _Available since v4.1._
     */
    modifier onlyRole(bytes32 role) {
        _checkRole(role);
        _;
    }

    function __AccessControl_init() internal onlyInitializing {
    }

    function __AccessControl_init_unchained() internal onlyInitializing {
    }
    /**
     * @dev See {IERC165-supportsInterface}.
     */
    function supportsInterface(bytes4 interfaceId) public view virtual override returns (bool) {
        return interfaceId == type(IAccessControlUpgradeable).interfaceId || super.supportsInterface(interfaceId);
    }

    /**
     * @dev Returns `true` if `account` has been granted `role`.
     */
    function hasRole(bytes32 role, address account) public view virtual override returns (bool) {
        return _roles[role].members[account];
    }

    /**
     * @dev Revert with a standard message if `_msgSender()` is missing `role`.
     * Overriding this function changes the behavior of the {onlyRole} modifier.
     *
     * Format of the revert message is described in {_checkRole}.
     *
     * _Available since v4.6._
     */
    function _checkRole(bytes32 role) internal view virtual {
        _checkRole(role, _msgSender());
    }

    /**
     * @dev Revert with a standard message if `account` is missing `role`.
     *
     * The format of the revert reason is given by the following regular expression:
     *
     *  /^AccessControl: account (0x[0-9a-f]{40}) is missing role (0x[0-9a-f]{64})$/
     */
    function _checkRole(bytes32 role, address account) internal view virtual {
        if (!hasRole(role, account)) {
            revert(
                string(
                    abi.encodePacked(
                        "AccessControl: account ",
                        StringsUpgradeable.toHexString(account),
                        " is missing role ",
                        StringsUpgradeable.toHexString(uint256(role), 32)
                    )
                )
            );
        }
    }

    /**
     * @dev Returns the admin role that controls `role`. See {grantRole} and
     * {revokeRole}.
     *
     * To change a role's admin, use {_setRoleAdmin}.
     */
    function getRoleAdmin(bytes32 role) public view virtual override returns (bytes32) {
        return _roles[role].adminRole;
    }

    /**
     * @dev Grants `role` to `account`.
     *
     * If `account` had not been already granted `role`, emits a {RoleGranted}
     * event.
     *
     * Requirements:
     *
     * - the caller must have ``role``'s admin role.
     *
     * May emit a {RoleGranted} event.
     */
    function grantRole(bytes32 role, address account) public virtual override onlyRole(getRoleAdmin(role)) {
        _grantRole(role, account);
    }

    /**
     * @dev Revokes `role` from `account`.
     *
     * If `account` had been granted `role`, emits a {RoleRevoked} event.
     *
     * Requirements:
     *
     * - the caller must have ``role``'s admin role.
     *
     * May emit a {RoleRevoked} event.
     */
    function revokeRole(bytes32 role, address account) public virtual override onlyRole(getRoleAdmin(role)) {
        _revokeRole(role, account);
    }

    /**
     * @dev Revokes `role` from the calling account.
     *
     * Roles are often managed via {grantRole} and {revokeRole}: this function's
     * purpose is to provide a mechanism for accounts to lose their privileges
     * if they are compromised (such as when a trusted device is misplaced).
     *
     * If the calling account had been revoked `role`, emits a {RoleRevoked}
     * event.
     *
     * Requirements:
     *
     * - the caller must be `account`.
     *
     * May emit a {RoleRevoked} event.
     */
    function renounceRole(bytes32 role, address account) public virtual override {
        require(account == _msgSender(), "AccessControl: can only renounce roles for self");

        _revokeRole(role, account);
    }

    /**
     * @dev Grants `role` to `account`.
     *
     * If `account` had not been already granted `role`, emits a {RoleGranted}
     * event. Note that unlike {grantRole}, this function doesn't perform any
     * checks on the calling account.
     *
     * May emit a {RoleGranted} event.
     *
     * [WARNING]
     * ====
     * This function should only be called from the constructor when setting
     * up the initial roles for the system.
     *
     * Using this function in any other way is effectively circumventing the admin
     * system imposed by {AccessControl}.
     * ====
     *
     * NOTE: This function is deprecated in favor of {_grantRole}.
     */
    function _setupRole(bytes32 role, address account) internal virtual {
        _grantRole(role, account);
    }

    /**
     * @dev Sets `adminRole` as ``role``'s admin role.
     *
     * Emits a {RoleAdminChanged} event.
     */
    function _setRoleAdmin(bytes32 role, bytes32 adminRole) internal virtual {
        bytes32 previousAdminRole = getRoleAdmin(role);
        _roles[role].adminRole = adminRole;
        emit RoleAdminChanged(role, previousAdminRole, adminRole);
    }

    /**
     * @dev Grants `role` to `account`.
     *
     * Internal function without access restriction.
     *
     * May emit a {RoleGranted} event.
     */
    function _grantRole(bytes32 role, address account) internal virtual {
        if (!hasRole(role, account)) {
            _roles[role].members[account] = true;
            emit RoleGranted(role, account, _msgSender());
        }
    }

    /**
     * @dev Revokes `role` from `account`.
     *
     * Internal function without access restriction.
     *
     * May emit a {RoleRevoked} event.
     */
    function _revokeRole(bytes32 role, address account) internal virtual {
        if (hasRole(role, account)) {
            _roles[role].members[account] = false;
            emit RoleRevoked(role, account, _msgSender());
        }
    }

    /**
     * @dev This empty reserved space is put in place to allow future versions to add new
     * variables without shifting down storage in the inheritance chain.
     * See https://docs.openzeppelin.com/contracts/4.x/upgradeable#storage_gaps
     */
    uint256[49] private __gap;
}

// contracts/core/VaultSettings.sol

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
contract VaultSettings is Initializable, AccessControlUpgradeable, IVaultSettings {
    error InvalidOwner();
    error WhiteListAlreadyEnabled();
    error WhiteListFailedToAdd();
    error WhiteListNotEnabled();
    error WhiteListFailedToRemove();
    error InvalidValue();
    error InvalidPercentage();
    error InvalidMaxLoanToValue();
    error InvalidAddress();

    // Gap before the roles to keep the storage layout consistent with version 1.3
    uint256[103] private __gapBefore;
    // Role definitions

    using EnumerableSet for EnumerableSet.AddressSet;
    /**
     * @dev The withdrawal fee percentage
     *
     * This private state variable holds the withdrawal fee percentage, represented as an integer.
     *
     * Default is 1%
     */
    uint256 private _withdrawalFee; // %

    /**
     * @dev The performance fee percentage.
     *
     * This private state variable holds the performance fee percentage, represented as an integer.
     */
    uint256 private _performanceFee; // 1%

    /**
     * @dev The address of the fee receiver.
     *
     * This private state variable holds the address of the fee receiver.
     * If set to the zero address, there is no fee receiver.
     */
    address private _feeReceiver; // No Fee Receiver
    /**
     * @dev The set of enabled accounts.
     *
     * This private state variable is an EnumerableSet of addresses representing the set of enabled accounts.
     */
    EnumerableSet.AddressSet private _enabledAccounts;

    /**
     * @dev Max Allowed Deposit per Wallet
     */
    uint256 private _maxDeposit;

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
     */
    function _initializeVaultSettings() public onlyInitializing {
        _withdrawalFee = 10 * 1e6; // 1%
        _performanceFee = 10 * 1e6; // 1%
        _feeReceiver = address(0); // No Fee Receiver
        _maxDeposit = 0;
    }

    /**
     * @dev Enables or disables an account in the whitelist.
     *
     * This function can only be called by the owner and is used to enable or disable an account
     * in the whitelist. Emits an {AccountWhiteList} event upon successful update.
     *
     * @param account The address of the account to be enabled or disabled.
     * @param enabled A boolean indicating whether the account should be enabled (true) or disabled (false) in the whitelist.
     *
     * Requirements:
     * - The caller must be the owner of the contract.
     */
    function enableAccount(address account, bool enabled) public onlyRole(ADMIN_ROLE) {
        if (enabled) {
            if (_enabledAccounts.contains(account)) revert WhiteListAlreadyEnabled();
            if (!_enabledAccounts.add(account)) revert WhiteListFailedToAdd();
        } else {
            if (!_enabledAccounts.contains(account)) revert WhiteListNotEnabled();
            if (!_enabledAccounts.remove(account)) revert WhiteListFailedToRemove();
        }
        emit AccountWhiteList(account, enabled);
    }

    /**
     * @dev Checks if an account is enabled in the whitelist.
     *
     * This function is externally callable and returns a boolean indicating whether the specified account
     * is enabled in the whitelist.
     *
     * @param account The address of the account to be checked.
     * @return enabled A boolean indicating whether the account is enabled (true) or not (false) in the whitelist.
     */
    function isAccountEnabled(address account) public view returns (bool) {
        return _enabledAccounts.length() == 0 || _enabledAccounts.contains(account);
    }

    /**
     * @dev Sets the withdrawal fee percentage.
     *
     * This function can only be called by the owner and is used to update the withdrawal fee percentage.
     * Emits a {WithdrawalFeeChanged} event upon successful update.
     *
     * @param fee The new withdrawal fee percentage to be set.
     *
     * Requirements:
     * - The caller must be the owner of the contract.
     * - The new withdrawal fee percentage must be a valid percentage value.
     */
    function setWithdrawalFee(uint256 fee) public onlyRole(ADMIN_ROLE) {
        if (fee >= PERCENTAGE_PRECISION) revert InvalidPercentage();
        _withdrawalFee = fee;
        emit WithdrawalFeeChanged(_withdrawalFee);
    }

    /**
     * @dev Retrieves the withdrawal fee percentage.
     *
     * This function is externally callable and returns the withdrawal fee percentage.
     *
     * @return fee The withdrawal fee percentage.
     */
    function getWithdrawalFee() public view returns (uint256) {
        return _withdrawalFee;
    }

    /**
     * @dev Sets the performance fee percentage.
     *
     * This function can only be called by the owner and is used to update the performance fee percentage.
     * Emits a {PerformanceFeeChanged} event upon successful update.
     *
     * @param fee The new performance fee percentage to be set.
     *
     * Requirements:
     * - The caller must be the owner of the contract.
     * - The new performance fee percentage must be a valid percentage value.
     */
    function setPerformanceFee(uint256 fee) external onlyRole(ADMIN_ROLE) {
        if (fee >= PERCENTAGE_PRECISION) revert InvalidPercentage();
        _performanceFee = fee;
        emit PerformanceFeeChanged(_performanceFee);
    }

    /**
     * @dev Retrieves the performance fee percentage.
     *
     * This function is externally callable and returns the performance fee percentage.
     *
     * @return fee The performance fee percentage.
     */
    function getPerformanceFee() public view returns (uint256) {
        return _performanceFee;
    }
    /**
     * @dev Sets the fee receiver address.
     *
     * This function can only be called by the owner and is used to update the fee receiver address.
     * Emits a {FeeReceiverChanged} event upon successful update.
     *
     * @param receiver The new fee receiver address to be set.
     *
     * Requirements:
     * - The caller must be the owner of the contract.
     * - The new fee receiver address must not be the zero address.
     */
    function setFeeReceiver(address receiver) external onlyRole(ADMIN_ROLE) {
        if (receiver == address(0)) revert InvalidAddress();
        _feeReceiver = receiver;
        emit FeeReceiverChanged(_feeReceiver);
    }

    /**
     * @dev Retrieves the fee receiver address.
     *
     * This function is externally callable and returns the fee receiver address.
     *
     * @return receiver The fee receiver address.
     */
    function getFeeReceiver() public view returns (address) {
        return _feeReceiver;
    }
    /**
     * @notice Retrieves the maximum deposit allowed in ETH.
     * @return The maximum deposit value in ETH.
     */
    function getMaxDeposit() public view returns (uint256) {
        return _maxDeposit;
    }

    /**
     * @notice Sets the maximum deposit allowed in ETH.
     * @param value The maximum deposit value to be set in ETH.
     */
    function setMaxDeposit(uint256 value) external onlyRole(ADMIN_ROLE) {
        _maxDeposit = value;
        emit MaxDepositChanged(value);
    }

    uint256[50] private __gap;
}

// contracts/core/MultiStrategy.sol

/**
 * @title MultiStrategy

 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 * @author Chef Kal-EL <chef.kal-el@bakerfi.xyz>
 *
 * @notice This contract is used to manage multiple strategies. The rebalancing is done based on the weights of the
 * strategies.
 */
abstract contract MultiStrategy is Initializable, AccessControlUpgradeable {
    /**
     * @notice Emitted when a new strategy is added to the MultiStrategy contract.
     * @param strategy The address of the added strategy.
     */
    event AddStrategy(address indexed strategy);
    /**
     * @notice Emitted when a strategy is removed from the MultiStrategy contract.
     * @param strategy The address of the removed strategy.
     */
    event RemoveStrategy(address indexed strategy);
    /**
     * @notice Emitted when the weights of the strategies are updated.
     * @param weights The new weights to set.
     */
    event WeightsUpdated(uint16[] indexed weights);
    /**
     * @notice Emitted when the maximum difference is updated.
     * @param maxDifference The new maximum difference to set.
     */
    event MaxDifferenceUpdated(uint256 indexed maxDifference);

    error InvalidStrategy(); // Thrown when an invalid strategy is provided (e.g., address is zero).
    error InvalidStrategyIndex(uint256 index); // Thrown when an invalid strategy index is accessed.
    error InvalidWeightsLength(); // Thrown when the weights array length is not equal to the strategies array length.
    error InvalidDeltasLength(); // Thrown when the deltas array length is not equal to the indexes array length.
    error InvalidStrategies(); // Thrown when the strategies array length is zero.
    error InvalidWeights(); // Thrown when the weights array length is zero.

    uint16 public constant MAX_TOTAL_WEIGHT = 10000;

    /**
     * @notice Array of strategies
     */
    IStrategy[] private _strategies; // Array of strategies
    /**
     * @notice Array of weights
     */
    uint16[] private _weights; // Array of weights
    /**
     * @notice Sum of all weights
     */
    uint16 private _totalWeight;

    /**
     * @notice Initializes the MultiStrategy contract with an array of strategy parameters.
     * @param istrategies An array of StrategyParams containing the strategies and their weights.
     * @dev This function sets the strategies and calculates the total weight of all strategies.
     */
    function _initMultiStrategy(IStrategy[] memory istrategies, uint16[] memory iweights) internal onlyInitializing {
        if (istrategies.length == 0) revert InvalidStrategies();
        if (iweights.length == 0) revert InvalidWeights();
        if (istrategies.length != iweights.length) revert InvalidWeightsLength();
        _strategies = istrategies;
        _weights = iweights;
        _totalWeight = 0;
        for (uint256 i = 0; i < istrategies.length; i++) {
            _totalWeight += iweights[i];
        }
        if (_totalWeight == 0) revert InvalidWeights();
        if (_totalWeight > 10000) revert InvalidWeights();
    }
    /**
     * @notice Sets the weights of the strategies.
     * @param iweights The new weights to set.
     * @dev Reverts if the weights array length is not equal to the strategies array length.
     */
    function setWeights(uint16[] memory iweights) public onlyRole(VAULT_MANAGER_ROLE) {
        if (iweights.length != _strategies.length) revert InvalidWeightsLength();
        _weights = iweights;
        _totalWeight = 0;

        for (uint256 i = 0; i < iweights.length; ) {
            _totalWeight += iweights[i];
            unchecked {
                i++;
            }
        }

        if (_totalWeight == 0 || _totalWeight > MAX_TOTAL_WEIGHT) revert InvalidWeights();

        emit WeightsUpdated(iweights);
    }

    /**
     * @notice Adds a new strategy to the MultiStrategy contract.
     * @param strategy The StrategyParams containing the strategy and its weight.
     * @dev Reverts if the strategy address is zero or if the weight is zero.
     */
    function addStrategy(IStrategy strategy) external onlyRole(VAULT_MANAGER_ROLE) {
        if (address(strategy) == address(0)) revert InvalidStrategy();
        _strategies.push(strategy);
        _weights.push(0);
        emit AddStrategy(address(strategy));
    }

    /**
     * @notice Returns the array of strategies.
     * @return An array of StrategyParams representing the strategies.
     */
    function strategies() external view returns (IStrategy[] memory) {
        return _strategies;
    }

    /**
     * @notice Returns the array of weights.
     * @return An array of uint8 representing the weights.
     */
    function weights() external view returns (uint16[] memory) {
        return _weights;
    }

    /**
     * @notice Returns the total weight of all strategies.
     * @return The total weight as a uint256.
     */
    function totalWeight() public view returns (uint16) {
        return _totalWeight;
    }

    /**
     * @notice Allocates assets to the strategies based on their weights.
     * @param amount The total amount of assets to allocate.
     * @dev This function deploys the calculated fractional amounts to each strategy.
     */
    function _allocateAssets(uint256 amount) internal returns (uint256 totalDeployed) {
        totalDeployed = 0;
        for (uint256 i = 0; i < _strategies.length; ) {
            uint256 fractAmount = (amount * _weights[i]) / _totalWeight;
            if (fractAmount > 0) {
                totalDeployed += IStrategy(_strategies[i]).deploy(fractAmount);
            }
            unchecked {
                i++;
            }
        }
    }
    /**
     * @notice Deallocates assets from the strategies based on their current weights.
     * @param amount The total amount of assets to deallocate.
     * @dev This function undeploys the calculated fractional amounts from each strategy.
     */
    function _deallocateAssets(uint256 amount) internal returns (uint256 totalUndeployed) {
        uint256[] memory currentAssets = new uint256[](_strategies.length);

        uint256 totalAssets = 0;
        uint256 strategiesLength = _strategies.length;

        for (uint256 i = 0; i < strategiesLength; i++) {
            currentAssets[i] = IStrategy(_strategies[i]).totalAssets();
            totalAssets += currentAssets[i];
        }
        totalUndeployed = 0;
        for (uint256 i = 0; i < strategiesLength; i++) {
            uint256 fractAmount = (amount * currentAssets[i]) / totalAssets;
            totalUndeployed += IStrategy(_strategies[i]).undeploy(fractAmount);
        }
    }

    /**
     * @notice Calculates the total assets managed by all strategies.
     * @return assets The total assets as a uint256.
     */
    function _totalAssets() internal view virtual returns (uint256 assets) {
        for (uint256 i = 0; i < _strategies.length; ) {
            assets += IStrategy(_strategies[i]).totalAssets();
            unchecked {
                i++;
            }
        }
        return assets;
    }

    function _harvestStrategies() internal returns (int256 balanceChange) {
        balanceChange = 0;
        for (uint256 i = 0; i < _strategies.length; i++) {
            balanceChange += IStrategy(_strategies[i]).harvest();
        }
    }

    /**
     * @notice Rebalances the strategies based on their target allocations.
     *  The caller functioin should make sure that the deltas are sorted with the positive deltas first and the negative deltas last
     *  This is to ensure that we deploy the strategies with the highest weights first and then the strategies with the lowest weights
     *  This is to ensure that we undeploy the strategies with the lowest weights first and then the strategies with the highest weights
     *
     * @param indexes The indexes of the strategies to rebalance.
     * @param deltas The delta amounts to rebalance.
     * @dev This function checks if the last allocation was within the minimum reallocation interval
     * and adjusts the allocations of each strategy accordingly.
     */
    function _rebalanceStrategies(uint256[] memory indexes, int256[] memory deltas) internal {
        uint256 totalStrategies = _strategies.length;
        if (deltas.length != indexes.length) revert InvalidDeltasLength();
        if (deltas.length != _strategies.length) revert InvalidDeltasLength();

        // Iterate through each strategy to adjust allocations
        for (uint256 i = 0; i < totalStrategies; i++) {
            // if the delta is 0, we don't need to rebalance the strategy
            if (deltas[i] == 0) continue;

            // if the delta is positive, we need to deploy the strategy
            if (deltas[i] > 0) {
                uint256 balanceOf = IERC20(_strategies[indexes[i]].asset()).balanceOf(address(this));
                uint256 amount = uint256(deltas[i]) > balanceOf ? balanceOf : uint256(deltas[i]);
                IStrategy(_strategies[indexes[i]]).deploy(amount);
                // if the delta is negative, we need to undeploy the strategy
            } else if (deltas[i] < 0) {
                IStrategy(_strategies[indexes[i]]).undeploy(uint256(-deltas[i]));
            }
        }
        // Deploy any dust balance to the highest weight strategy
        uint256 dustBalance = IERC20(_strategies[0].asset()).balanceOf(address(this));
        if (dustBalance > 0) {
            uint256 highestWeightIndex = 0;
            uint16 highestWeight = 0;
            for (uint256 i = 0; i < totalStrategies; i++) {
                if (_weights[i] > highestWeight) {
                    highestWeight = _weights[i];
                    highestWeightIndex = i;
                }
            }
            IStrategy(_strategies[highestWeightIndex]).deploy(dustBalance);
        }
    }

    /**
     * @notice Removes a strategy from the MultiStrategy contract.
     * @param index The index of the strategy to remove.
     * @dev Reverts if the index is out of bounds. The last strategy is moved to the removed index.
     * This function also handles the undeployment of assets from the strategy being removed and
     * rebalances the remaining strategies.
     */
    function removeStrategy(uint256 index) external onlyRole(VAULT_MANAGER_ROLE) {
        // Validate the index to ensure it is within bounds
        if (index >= _strategies.length) revert InvalidStrategyIndex(index);

        // Retrieve the total assets managed by the strategy to be removed
        uint256 strategyAssets = _strategies[index].totalAssets();

        // Update the total weight and mark the weight of the removed strategy as zero
        _totalWeight -= _weights[index];
        _weights[index] = 0;

        // If the strategy has assets, undeploy them and allocate accordingly
        if (strategyAssets > 0) {
            IStrategy(_strategies[index]).undeploy(strategyAssets);
            _allocateAssets(strategyAssets);
        }

        // Move the last strategy to the index of the removed strategy to maintain array integrity
        uint256 lastIndex = _strategies.length - 1;
        if (index < lastIndex) {
            _strategies[index] = _strategies[lastIndex];
            _weights[index] = _weights[lastIndex];
        }

        emit RemoveStrategy(address(_strategies[lastIndex]));
        // Remove the last strategy and weight from the arrays
        _strategies.pop();
        _weights.pop();
    }
}

// node_modules/@openzeppelin/contracts-upgradeable/token/ERC20/extensions/ERC20PermitUpgradeable.sol

// OpenZeppelin Contracts (last updated v4.9.4) (token/ERC20/extensions/ERC20Permit.sol)

/**
 * @dev Implementation of the ERC20 Permit extension allowing approvals to be made via signatures, as defined in
 * https://eips.ethereum.org/EIPS/eip-2612[EIP-2612].
 *
 * Adds the {permit} method, which can be used to change an account's ERC20 allowance (see {IERC20-allowance}) by
 * presenting a message signed by the account. By not relying on `{IERC20-approve}`, the token holder account doesn't
 * need to send a transaction, and thus is not required to hold Ether at all.
 *
 * _Available since v3.4._
 *
 * @custom:storage-size 51
 */
abstract contract ERC20PermitUpgradeable is Initializable, ERC20Upgradeable, IERC20PermitUpgradeable, EIP712Upgradeable {
    using CountersUpgradeable for CountersUpgradeable.Counter;

    mapping(address => CountersUpgradeable.Counter) private _nonces;

    // solhint-disable-next-line var-name-mixedcase
    bytes32 private constant _PERMIT_TYPEHASH =
        keccak256("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)");
    /**
     * @dev In previous versions `_PERMIT_TYPEHASH` was declared as `immutable`.
     * However, to ensure consistency with the upgradeable transpiler, we will continue
     * to reserve a slot.
     * @custom:oz-renamed-from _PERMIT_TYPEHASH
     */
    // solhint-disable-next-line var-name-mixedcase
    bytes32 private _PERMIT_TYPEHASH_DEPRECATED_SLOT;

    /**
     * @dev Initializes the {EIP712} domain separator using the `name` parameter, and setting `version` to `"1"`.
     *
     * It's a good idea to use the same `name` that is defined as the ERC20 token name.
     */
    function __ERC20Permit_init(string memory name) internal onlyInitializing {
        __EIP712_init_unchained(name, "1");
    }

    function __ERC20Permit_init_unchained(string memory) internal onlyInitializing {}

    /**
     * @inheritdoc IERC20PermitUpgradeable
     */
    function permit(
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) public virtual override {
        require(block.timestamp <= deadline, "ERC20Permit: expired deadline");

        bytes32 structHash = keccak256(abi.encode(_PERMIT_TYPEHASH, owner, spender, value, _useNonce(owner), deadline));

        bytes32 hash = _hashTypedDataV4(structHash);

        address signer = ECDSAUpgradeable.recover(hash, v, r, s);
        require(signer == owner, "ERC20Permit: invalid signature");

        _approve(owner, spender, value);
    }

    /**
     * @inheritdoc IERC20PermitUpgradeable
     */
    function nonces(address owner) public view virtual override returns (uint256) {
        return _nonces[owner].current();
    }

    /**
     * @inheritdoc IERC20PermitUpgradeable
     */
    // solhint-disable-next-line func-name-mixedcase
    function DOMAIN_SEPARATOR() external view override returns (bytes32) {
        return _domainSeparatorV4();
    }

    /**
     * @dev "Consume a nonce": return the current value and increment.
     *
     * _Available since v4.1._
     */
    function _useNonce(address owner) internal virtual returns (uint256 current) {
        CountersUpgradeable.Counter storage nonce = _nonces[owner];
        current = nonce.current();
        nonce.increment();
    }

    /**
     * @dev This empty reserved space is put in place to allow future versions to add new
     * variables without shifting down storage in the inheritance chain.
     * See https://docs.openzeppelin.com/contracts/4.x/upgradeable#storage_gaps
     */
    uint256[49] private __gap;
}

// contracts/core/VaultBase.sol

/**
 * @title BakerFi Vault Base 🧑‍🍳
 *
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 * @author Chef Kal-EL <chef.kal-el@bakerfi.xyz>
 *
 * @dev This contract serves as the base for the BakerFi Vault, providing core functionalities
 * for managing assets, deposits, withdrawals, and rebalancing strategies.
 * It inherits from several OpenZeppelin contracts to ensure security and upgradeability.
 */
abstract contract VaultBase is
    AccessControlUpgradeable,
    PausableUpgradeable,
    ReentrancyGuardUpgradeable,
    ERC20Upgradeable,
    VaultSettings,
    UseWETH,
    IVault
{
    using RebaseLibrary for Rebase;
    using SafeERC20Upgradeable for IERC20Upgradeable;
    using AddressUpgradeable for address;
    using AddressUpgradeable for address payable;
    using MathLibrary for uint256;

    // Custom errors for better gas efficiency
    error InvalidAmount();
    error InvalidAssetsState();
    error InvalidAsset();
    error MaxDepositReached();
    error NotEnoughBalanceToWithdraw();
    error NoAssetsToWithdraw();
    error NoPermissions();
    error InvalidShareBalance();
    error InvalidReceiver();
    error NoAllowance();

    uint256 private constant _MINIMUM_SHARE_BALANCE = 1000;
    uint256 private constant _ONE = 1e18;

    /**
     * @dev Modifier to restrict access to whitelisted accounts.
     */
    modifier onlyWhiteListed() {
        if (!isAccountEnabled(msg.sender)) revert NoPermissions();
        _;
    }

    /// @custom:oz-upgrades-unsafe-allow constructor
    constructor() {
        _disableInitializers();
    }

    /**
     * @dev Fallback function to accept ETH transfers.
     * Reverts if the sender is not the wrapped ETH address.
     */
    receive() external payable override {
        if (msg.sender != wETHA()) revert ETHTransferNotAllowed(msg.sender);
    }
    /**
     * @dev Initializes the base contract with the specified parameters.
     * @param initialOwner The address of the initial owner of the vault.
     * @param tokenName The name of the token.
     * @param tokenSymbol The symbol of the token.
     * @param weth The address of the wrapped ETH contract.
     */
    function _initializeBase(
        address initialOwner,
        string calldata tokenName,
        string calldata tokenSymbol,
        address weth
    ) internal {
        __ERC20_init(tokenName, tokenSymbol);
        _initUseWETH(weth);
        if (initialOwner == address(0)) revert InvalidOwner();
        _initializeVaultSettings();
        __AccessControl_init();
        _setupRole(ADMIN_ROLE, initialOwner);
        _setupRole(VAULT_MANAGER_ROLE, initialOwner);
        _setupRole(PAUSER_ROLE, initialOwner);
    }

    /**
     * @dev Returns the address of the asset being managed by the vault.
     * @return The address of the asset.
     */
    function _asset() internal view virtual returns (address);

    /**
     * @dev Returns the total amount of assets managed by the vault.
     * @return amount The total assets amount.
     */
    function _totalAssets() internal view virtual returns (uint256 amount);

    /**
     * @dev Harvests the assets and returns the balance change.
     * @return balanceChange The change in balance after harvesting.
     */
    function _harvest() internal virtual returns (int256 balanceChange);

    /**
     * @dev Deploys the specified amount of assets.
     * @param assets The amount of assets to deploy.
     * @return The amount of assets deployed.
     */
    function _deploy(uint256 assets) internal virtual returns (uint256);

    /**
     * @dev Undeploys the specified amount of assets.
     * @param assets The amount of assets to undeploy.
     * @return The amount of assets undeployed.
     */
    function _undeploy(uint256 assets) internal virtual returns (uint256);

    function _harvestAndMintFees() internal {
        uint256 currentPosition = _totalAssets();
        if (currentPosition == 0) {
            return;
        }
        int256 balanceChange = _harvest();
        if (balanceChange > 0) {
            address feeReceiver = getFeeReceiver();
            uint256 performanceFee = getPerformanceFee();
            if (feeReceiver != address(this) && feeReceiver != address(0) && performanceFee > 0) {
                uint256 feeInEth = uint256(balanceChange) * performanceFee;
                uint256 sharesToMint = feeInEth.mulDivUp(totalSupply(), currentPosition * PERCENTAGE_PRECISION);
                _mint(feeReceiver, sharesToMint);
            }
        }
    }

    /**
     * @dev Returns the maximum number of shares that can be minted.
     * @return maxShares The maximum number of shares.
     */
    function maxMint(address) external pure override returns (uint256 maxShares) {
        return type(uint256).max;
    }

    /**
     * @dev Returns the amount of assets that can be obtained for a given number of shares.
     * @param shares The number of shares to preview.
     * @return assets The amount of assets corresponding to the shares.
     */
    function previewMint(uint256 shares) external view override returns (uint256 assets) {
        assets = this.convertToAssets(shares);
    }

    /**
     * @dev Mints shares for the specified receiver in exchange for assets.
     * @param shares The number of shares to mint.
     * @param receiver The address of the receiver.
     * @return assets The amount of assets used to mint the shares.
     */
    function mint(
        uint256 shares,
        address receiver
    ) external override nonReentrant whenNotPaused onlyWhiteListed returns (uint256 assets) {
        if (shares == 0) revert InvalidAmount();
        assets = this.convertToAssets(shares);
        IERC20Upgradeable(_asset()).safeTransferFrom(msg.sender, address(this), assets);
        _depositInternal(assets, receiver);
    }

    /**
     * @dev Returns the maximum amount of assets that can be deposited.
     * @return maxAssets The maximum amount of assets.
     */
    function maxDeposit(address) external pure override returns (uint256 maxAssets) {
        return type(uint256).max;
    }

    /**
     * @dev Returns the number of shares that can be obtained for a given amount of assets.
     * @param assets The amount of assets to preview.
     * @return shares The number of shares corresponding to the assets.
     */
    function previewDeposit(uint256 assets) external view override returns (uint256 shares) {
        shares = this.convertToShares(assets);
    }

    /**
     * @dev Deposits native ETH into the vault, wrapping it in WETH.
     * @param receiver The address of the receiver.
     * @return shares The number of shares minted for the deposit.
     */
    function depositNative(
        address receiver
    ) external payable nonReentrant whenNotPaused onlyWhiteListed returns (uint256 shares) {
        if (msg.value == 0) revert InvalidAmount();
        if (_asset() != wETHA()) revert InvalidAsset();
        //  Wrap ETH
        wETHA().functionCallWithValue(abi.encodeWithSignature("deposit()"), msg.value);
        return _depositInternal(msg.value, receiver);
    }

    /**
     * @dev Deposits the specified amount of assets into the vault.
     * @param assets The amount of assets to deposit.
     * @param receiver The address of the receiver.
     * @return shares The number of shares minted for the deposit.
     */
    function deposit(
        uint256 assets,
        address receiver
    ) external override nonReentrant whenNotPaused onlyWhiteListed returns (uint256 shares) {
        if (assets == 0) revert InvalidAmount();
        IERC20Upgradeable(_asset()).safeTransferFrom(msg.sender, address(this), assets);
        return _depositInternal(assets, receiver);
    }

    /**
     * @dev Internal function to handle the deposit logic.
     * @param assets The amount of assets to deposit.
     * @param receiver The address of the receiver.
     * @return shares The number of shares minted for the deposit.
     */
    function _depositInternal(uint256 assets, address receiver) private returns (uint256 shares) {
        if (receiver == address(0)) revert InvalidReceiver();
        // Fetch price options from settings
        // Get the total assets and total supply
        Rebase memory total = Rebase(totalAssets(), totalSupply());

        // Check if the Rebase is uninitialized or both base and elastic are positive
        if (!((total.elastic == 0 && total.base == 0) || (total.base > 0 && total.elastic > 0))) {
            revert InvalidAssetsState();
        }

        // Check if deposit exceeds the maximum allowed per wallet
        uint256 maxDepositLocal = getMaxDeposit();
        if (maxDepositLocal > 0) {
            uint256 depositInAssets = (balanceOf(msg.sender) * _ONE) / tokenPerAsset();
            uint256 newBalance = assets + depositInAssets;
            if (newBalance > maxDepositLocal) revert MaxDepositReached();
        }

        uint256 deployedAmount = _deploy(assets);

        // Calculate shares to mint
        shares = total.toBase(deployedAmount, false);

        // Prevent inflation attack for the first deposit
        if (total.base == 0 && shares < _MINIMUM_SHARE_BALANCE) {
            revert InvalidShareBalance();
        }

        // Mint shares to the receiver
        _mint(receiver, shares);

        // Emit deposit event
        emit Deposit(msg.sender, receiver, assets, shares);
    }

    /**
     * @dev Returns the maximum amount of assets that can be withdrawn by a shareholder.
     * @param shareHolder The address of the shareholder.
     * @return maxAssets The maximum amount of assets that can be withdrawn.
     */
    function maxWithdraw(address shareHolder) external view override returns (uint256 maxAssets) {
        maxAssets = this.convertToAssets(balanceOf(shareHolder));
    }

    /**
     * @dev Returns the number of shares that can be obtained for a given amount of assets.
     * @param assets The amount of assets to preview.
     * @return shares The number of shares corresponding to the assets.
     */
    function previewWithdraw(uint256 assets) external view override returns (uint256 shares) {
        shares = this.convertToShares(assets);
    }

    /**
     * @dev Withdraws native ETH from the vault.
     * @param assets The amount of assets to withdraw.
     * @return shares The number of shares burned for the withdrawal.
     */
    function withdrawNative(
        uint256 assets
    ) external override nonReentrant whenNotPaused onlyWhiteListed returns (uint256 shares) {
        if (_asset() != wETHA()) revert InvalidAsset();
        shares = this.convertToShares(assets);
        _redeemInternal(shares, msg.sender, msg.sender, true);
    }

    /**
     * @dev Redeems native ETH from the vault for the specified number of shares.
     * @param shares The number of shares to redeem.
     * @return assets The amount of assets withdrawn.
     */
    function redeemNative(
        uint256 shares
    ) external override nonReentrant whenNotPaused onlyWhiteListed returns (uint256 assets) {
        if (_asset() != wETHA()) revert InvalidAsset();
        assets = _redeemInternal(shares, msg.sender, msg.sender, true);
    }

    /**
     * @dev Withdraws the specified amount of assets from the vault.
     * @param assets The amount of assets to withdraw.
     * @param receiver The address of the receiver.
     * @param holder The owner of the assets to withdraw.
     * @return shares The number of shares burned for the withdrawal.
     */
    function withdraw(
        uint256 assets,
        address receiver,
        address holder
    ) external override nonReentrant whenNotPaused onlyWhiteListed returns (uint256 shares) {
        shares = this.convertToShares(assets);
        return _redeemInternal(shares, receiver, holder, false);
    }

    /**
     * @dev Returns the maximum number of shares that can be redeemed by a shareholder.
     * @param shareHolder The address of the shareholder.
     * @return maxShares The maximum number of shares that can be redeemed.
     */
    function maxRedeem(address shareHolder) external view override returns (uint256 maxShares) {
        maxShares = balanceOf(shareHolder);
    }

    /**
     * @dev Returns the amount of assets that can be obtained for a given number of shares.
     * @param shares The number of shares to preview.
     * @return assets The amount of assets corresponding to the shares.
     */
    function previewRedeem(uint256 shares) external view override returns (uint256 assets) {
        assets = this.convertToAssets(shares);
    }

    /**
     * @dev Redeems the specified number of shares for assets.
     * @param shares The number of shares to redeem.
     * @param receiver The address of the receiver.
     * @param holder The owner of the shares to redeem.
     * @return retAmount The amount of assets received after redemption.
     */
    function redeem(
        uint256 shares,
        address receiver,
        address holder
    ) external override nonReentrant onlyWhiteListed whenNotPaused returns (uint256 retAmount) {
        return _redeemInternal(shares, receiver, holder, false);
    }

    /**
     * @dev Internal function to handle the redemption logic.
     * @param shares The number of shares to redeem.
     * @param receiver The address of the receiver.
     * @param holder The owner of the shares to redeem.
     * @param shouldRedeemETH Whether to redeem as ETH.
     * @return retAmount The amount of assets received after redemption.
     */
    function _redeemInternal(
        uint256 shares,
        address receiver,
        address holder,
        bool shouldRedeemETH
    ) private returns (uint256 retAmount) {
        if (shares == 0) revert InvalidAmount();
        if (receiver == address(0)) revert InvalidReceiver();
        if (balanceOf(holder) < shares) revert NotEnoughBalanceToWithdraw();

        // Transfer shares to the contract if sender is not the holder
        if (msg.sender != holder) {
            if (allowance(holder, msg.sender) < shares) revert NoAllowance();
            transferFrom(holder, msg.sender, shares);
        }

        // Calculate the amount to withdraw based on shares
        uint256 withdrawAmount = (shares * totalAssets()) / totalSupply();
        if (withdrawAmount == 0) revert NoAssetsToWithdraw();

        uint256 amount = _undeploy(withdrawAmount);
        uint256 fee = 0;
        uint256 remainingShares = totalSupply() - shares;

        // Ensure a minimum number of shares are maintained to prevent ratio distortion
        if (remainingShares < _MINIMUM_SHARE_BALANCE && remainingShares != 0) {
            revert InvalidShareBalance();
        }

        _burn(msg.sender, shares);

        // Calculate and handle withdrawal fees
        if (getWithdrawalFee() != 0 && getFeeReceiver() != address(0)) {
            fee = amount.mulDivUp(getWithdrawalFee(), PERCENTAGE_PRECISION);

            if (shouldRedeemETH && _asset() == wETHA()) {
                unwrapETH(amount);
                payable(receiver).sendValue(amount - fee);
                payable(getFeeReceiver()).sendValue(fee);
            } else {
                IERC20Upgradeable(_asset()).transfer(receiver, amount - fee);
                IERC20Upgradeable(_asset()).transfer(getFeeReceiver(), fee);
            }
        } else {
            if (shouldRedeemETH) {
                unwrapETH(amount);
                payable(receiver).sendValue(amount);
            } else {
                IERC20Upgradeable(_asset()).transfer(receiver, amount);
            }
        }

        emit Withdraw(msg.sender, receiver, holder, amount - fee, shares);
        retAmount = amount - fee;
    }

    /**
     * @dev Retrieves the total assets controlled/belonging to the vault.
     * @return amount The total assets under management by the strategy.
     */
    function totalAssets() public view override returns (uint256 amount) {
        amount = _totalAssets();
    }

    /**
     * @dev Converts the specified amount of ETH/ERC20 to shares.
     * @param assets The amount of assets to be converted to shares.
     * @return shares The calculated number of shares.
     */
    function convertToShares(uint256 assets) external view override returns (uint256 shares) {
        Rebase memory total = Rebase(totalAssets(), totalSupply());
        shares = total.toBase(assets, false);
    }

    /**
     * @dev Converts the specified number of shares to ETH/ERC20.
     * @param shares The number of shares to be converted to assets.
     * @return assets The calculated amount of assets.
     */
    function convertToAssets(uint256 shares) external view override returns (uint256 assets) {
        Rebase memory total = Rebase(totalAssets(), totalSupply());
        assets = total.toElastic(shares, false);
    }

    /**
     * @dev Returns the address of the asset being managed by the vault.
     * @return The address of the asset.
     */
    function asset() external view override returns (address) {
        return _asset();
    }

    /**
     * @dev Retrieves the token-to-Asset exchange rate.
     * @return rate The calculated token-to-ETH exchange rate.
     */
    function tokenPerAsset() public view returns (uint256) {
        uint256 totalAssetsValue = totalAssets();

        if (totalSupply() == 0 || totalAssetsValue == 0) {
            return _ONE;
        }

        return (totalSupply() * _ONE) / totalAssetsValue;
    }

    /**
     * @dev Pauses the Contract.
     * Only the Owner is able to pause the vault.
     * When the contract is paused, deposit, withdraw, and rebalance cannot be called without reverting.
     */
    function pause() external onlyRole(PAUSER_ROLE) {
        _pause();
    }

    /**
     * @dev Unpauses the contract.
     * Only the Owner is able to unpause the vault.
     */
    function unpause() external onlyRole(PAUSER_ROLE) {
        _unpause();
    }

    /**
     * @dev This empty reserved space is put in place to allow future versions to add new
     * variables without shifting down storage in the inheritance chain.
     */
    uint256[100] private __gap;
}

// contracts/core/MultiStrategyVault.sol

/**
 * @title MultiStrategyVault 🏦🧑‍🍳
 *
 * @author Chef Kenji <chef.kenji@bakerfi.xyz>
 * @author Chef Kal-EL <chef.kal-el@bakerfi.xyz>
 *
 * @dev The MultiStrategyVault is orchestration vault capable of managing multiple investment strategies.
 *
 * This is smart contract where the users deposit their ETH or an ERC-20 and receives a share of the pool <x>brETH.
 * A share of the pool is an ERC-20 Token (transferable) and could be used to later to withdraw their
 * owned amount of the pool that could contain (Assets + Yield).
 * This vault could use to support multiple strategies and deploy the capital on the strategies based on
 * set of weights defined by the vault manager.
 *
 * The Contract is able to charge a performance and withdraw fee that is send to the treasury
 * owned account when the fees are set by the deploy owner.
 *
 * The Vault is Pausable by a pauser role and is using the settings to retrieve base
 * performance, withdraw fees and other kind of settings.
 *
 * During the beta phase only whitelisted addresses are able to deposit and withdraw
 *
 * The Contract is upgradeable and can use a BakerProxy in front of.
 *
 * The Vault follows the ERC-4626 Specification and can be integrated by any Aggregator
 *
 * The rebalance function is allowing a flexible external management through the vault manager role
 * and could be used to perform a variety of operations such as harvesting yield, rebalancing assets,
 * changing weights, and other strategic actions that could be programmed by an external agent
 * that have access to external information and implement healthy procedures in order to protect the
 * vault or impreove the vault performance.
 */
contract MultiStrategyVault is VaultBase, MultiStrategy {
    using SafeERC20Upgradeable for IERC20Upgradeable;

    // Rebalance commands
    uint8 public constant HARVEST_VAULT = 0x01; //
    uint8 public constant REBALANCE_STRATEGIES = 0x02; //
    uint8 public constant CHANGE_WEIGHTS = 0x03; //

    address internal _strategyAsset;

    /// @custom:oz-upgrades-unsafe-allow constructor
    constructor() VaultBase() {
        _disableInitializers(); // Prevents the contract from being initialized more than once
    }

    /**
     * @dev Initializes the contract with specified parameters.
     *
     * This function is designed to be called only once during the contract deployment.
     * It sets up the initial state of the contract, including ERC20 and ERC20Permit
     * initializations, ownership transfer, and configuration of the VaultRegistry
     * and Strategy.
     *
     * @param initialOwner The address that will be set as the initial owner of the contract.
     * @param tokenName The name of the token.
     * @param tokenSymbol The symbol of the token.
     * @param iAsset The asset to be set as the asset for this contract.
     * @param istrategies The IStrategy contracts to be set as the strategies for this contract.
     * @param iweights The weights of the strategies.
     * @param weth The WETH contract to be set as the WETH for this contract.
     *
     * Emits an {OwnershipTransferred} event and initializes ERC20 and ERC20Permit features.
     * It also ensures that the initialOwner is a valid address and sets up the VaultRegistry
     * and Strategy for the contract.
     */
    function initialize(
        address initialOwner,
        string calldata tokenName,
        string calldata tokenSymbol,
        address iAsset,
        IStrategy[] memory istrategies,
        uint16[] memory iweights,
        address weth
    ) public initializer {
        _initializeBase(initialOwner, tokenName, tokenSymbol, weth); // Initializes the base contract with the provided parameters
        _initMultiStrategy(istrategies, iweights); // Initializes the multi-strategy with the provided strategies and weights

        // Check if the asset is valid
        if (iAsset == address(0)) revert InvalidAsset();
        _strategyAsset = iAsset;

        for (uint256 i = 0; i < istrategies.length; i++) {
            // Check if the strategy asset is the same as the asset of the vault
            if (istrategies[i].asset() != iAsset) revert InvalidAsset(); // Reverts if the strategy asset does not match the vault asset
            // Approve the strategies to spend assets that are deposited in the vault
            IERC20Upgradeable(iAsset).safeApprove(address(istrategies[i]), type(uint256).max); // Approves the strategy to spend the maximum amount of the asset
        }
    }

    /**
     * @dev Harvests the yield from the strategies.
     *
     * This function calls the internal _harvestStrategies function to collect yield
     * from all strategies and returns the balance change.
     *
     * @return balanceChange The change in balance after harvesting.
     */
    function _harvest() internal virtual override returns (int256 balanceChange) {
        balanceChange = _harvestStrategies(); // Calls the strategy harvest function and returns the balance change
    }

    /**
     * @dev Deploys assets to the strategies.
     *
     * This function allocates the specified amount of assets to the strategies
     * and returns the amount that was deployed.
     *
     * @param assets The amount of assets to deploy.
     * @return deployedAmount The amount of assets that were successfully deployed.
     */
    function _deploy(uint256 assets) internal virtual override returns (uint256 deployedAmount) {
        deployedAmount = _allocateAssets(assets); // Allocates assets to the strategies and returns the deployed amount
    }

    /**
     * @dev Undeploys assets from the strategies.
     *
     * This function deallocates the specified amount of assets from the strategies
     * and returns the amount that was undeployed.
     *
     * @param assets The amount of assets to undeploy.
     * @return undeployedAmount The amount of assets that were successfully undeployed.
     */
    function _undeploy(uint256 assets) internal virtual override returns (uint256 undeployedAmount) {
        undeployedAmount = _deallocateAssets(assets); // Deallocates assets from the strategies and returns the undeployed amount
    }

    /**
     * @dev Calculates the total assets managed by the vault.
     *
     * This function overrides the totalAssets function from both VaultBase and MultiStrategy
     * to return the total assets managed by the strategies.
     *
     * @return assets The total assets managed by the vault.
     */
    function _totalAssets() internal view virtual override(VaultBase, MultiStrategy) returns (uint256 assets) {
        assets = MultiStrategy._totalAssets(); // Calls the totalAssets function from MultiStrategy to get the total assets
    }

    function _asset() internal view virtual override returns (address) {
        return _strategyAsset;
    }

    /**
     * @dev Rebalances the vault's assets.
     *
     * @param commands The commands to rebalance the vault's assets.
     *
     * The commands are an array of RebalanceCommand structs, each containing an action and data.
     * The action is the type of the command and the data is the data of the command.
     *
     * This rebalance support 3 actions:
     *
     * - HARVEST_VAULT: Harvests the yield from the strategies.
     * - REBALANCE_STRATEGIES: Rebalances the strategies based on the deltas.
     * - CHANGE_WEIGHTS: Changes the weights of the strategies.
     *
     * @return success Whether the rebalancing was successful.
     */
    function rebalance(
        IVault.RebalanceCommand[] calldata commands
    ) external override nonReentrant onlyRole(VAULT_MANAGER_ROLE) returns (bool success) {
        success = true;
        uint256 numCommands = commands.length;
        for (uint256 i = 0; i < numCommands; ) {
            if (commands[i].action == HARVEST_VAULT) {
                _harvestAndMintFees();
            } else if (commands[i].action == REBALANCE_STRATEGIES) {
                (uint256[] memory indexes, int256[] memory deltas) = abi.decode(
                    commands[i].data,
                    (uint256[], int256[])
                );
                _rebalanceStrategies(indexes, deltas);
            } else if (commands[i].action == CHANGE_WEIGHTS) {
                uint16[] memory weights = abi.decode(commands[i].data, (uint16[]));
                setWeights(weights);
            }
            unchecked {
                i++;
            }
        }
    }

    uint256[50] private __gap;
}


contract Vault is VaultBase {
    /**
     * @dev The IStrategy contract representing the strategy for deploying/undeploying assets.
     *
     * This private state variable holds the reference to the IStrategy contract,
     * which defines the strategy for managing assets within the current contract.
     */
    IStrategy private _strategy;

    /**
     * @dev The address of the asset being managed by the strategy.
     */
    address internal _strategyAsset;
    uint8 private constant _VAULT_VERSION = 3;

    using MathLibrary for uint256;

    /// @custom:oz-upgrades-unsafe-allow constructor
    constructor() VaultBase() {
        _disableInitializers(); // Prevents the contract from being initialized again
    }

    uint8 public constant HARVEST_VAULT = 0x01; //

    using SafeERC20Upgradeable for IERC20Upgradeable;

    /**
     * @dev Initializes the contract with specified parameters.
     *
     * This function is designed to be called only once during the contract deployment.
     * It sets up the initial state of the contract, including ERC20 and ERC20Permit
     * initializations, ownership transfer, and configuration of the VaultRegistry
     * and Strategy.
     *
     * @param initialOwner The address that will be set as the initial owner of the contract.
     * @param tokenName The name of the token.
     * @param tokenSymbol The symbol of the token.
     * @param iAsset The address of the asset.
     * @param strategy The IStrategy contract to be set as the strategy for this contract.
     * @param weth The WETH contract to be set as the WETH for this contract.
     *
     * Emits an {OwnershipTransferred} event and initializes ERC20 and ERC20Permit features.
     * It also ensures that the initialOwner is a valid address and sets up the VaultRegistry
     * and Strategy for the contract.
     */
    function initialize(
        address initialOwner,
        string calldata tokenName,
        string calldata tokenSymbol,
        address iAsset,
        IStrategy strategy,
        address weth
    ) public initializer {
        _initializeBase(initialOwner, tokenName, tokenSymbol, weth); // Initializes the base contract
        if (iAsset == address(0)) revert InvalidAsset();
        _strategyAsset = iAsset;
        _strategy = strategy; // Sets the strategy for the vault
    }

    /**
     * @dev Function to rebalance the strategy, prevent a liquidation and pay fees
     * to the protocol by minting shares to the fee receiver.
     *
     * This function is externally callable and is marked as non-reentrant.
     * It triggers the harvest operation on the strategy, calculates the balance change,
     * and applies performance fees if applicable.
     *
     * @return balanceChange The change in balance after the rebalance operation.
     */
    function _harvest() internal virtual override returns (int256 balanceChange) {
        return _strategy.harvest(); // Calls the harvest function of the strategy
    }

    /**
     * @dev Deposits Ether into the contract and mints vault's shares for the specified receiver.
     *
     * This function is externally callable, marked as non-reentrant, and could be restricted
     * to whitelisted addresses. It performs various checks, including verifying that
     * the deposited amount is valid, the Rebase state is initialized, and executes
     * the strategy's `deploy` function to handle the deposit.
     *
     * @param assets The amount of assets to be deployed.
     * @return deployedAmount The number of deployed assets.
     */
    function _deploy(uint256 assets) internal virtual override returns (uint256 deployedAmount) {
        // Approve the strategy to spend assets
        IERC20Upgradeable(_strategyAsset).safeApprove(address(_strategy), assets);
        // Deploy assets via the strategy
        deployedAmount = _strategy.deploy(assets); // Calls the deploy function of the strategy
    }

    /**
     * @dev Withdraws a specified number of vault's shares, converting them to ETH/ERC20 and
     * transferring to the caller.
     *
     * This function is externally callable, marked as non-reentrant, and restricted to whitelisted addresses.
     * It checks for sufficient balance, non-zero share amount, and undeploys the capital from the strategy
     * to handle the withdrawal request. It calculates withdrawal fees, transfers Ether to the caller, and burns the
     * withdrawn shares.
     *
     * @param assets The number of shares to be withdrawn.
     * @return retAmount The amount of ETH/ERC20 withdrawn after fees.
     *
     * Emits a {Withdraw} event after successfully handling the withdrawal.
     */
    function _undeploy(uint256 assets) internal virtual override returns (uint256 retAmount) {
        retAmount = _strategy.undeploy(assets); // Calls the undeploy function of the strategy
    }

    /**
     * @dev Retrieves the total assets controlled/belonging to the vault.
     *
     * This function is publicly accessible and provides a view of the total assets currently
     * deployed in the current strategy. This function uses the latest prices
     * and does not revert on outdated prices.
     *
     * @return amount The total assets under management by the strategy.
     */
    function _totalAssets() internal view virtual override returns (uint256 amount) {
        amount = _strategy.totalAssets(); // Calls the totalAssets function of the strategy
    }

    function _asset() internal view virtual override returns (address) {
        return _strategyAsset;
    }

    /**
     * @dev Rebalances the strategy, prevent a liquidation and pay fees
     * to protocol by minting shares to the fee receiver
     *
     * This rebalance support 1 action:
     *
     * - HARVEST_VAULT: Harvests the yield from the strategy
     *
     * @param commands The data to be passed to the rebalance function
     * @return success The success of the rebalance operation.
     */
    function rebalance(
        IVault.RebalanceCommand[] calldata commands
    ) external override nonReentrant onlyRole(VAULT_MANAGER_ROLE) returns (bool success) {
        success = true;
        uint256 numCommands = commands.length;
        for (uint256 i = 0; i < numCommands; ) {
            if (commands[i].action == HARVEST_VAULT) {
                _harvestAndMintFees();
            }
            unchecked {
                i++;
            }
        }
    }

    uint256[50] private __gap;
}