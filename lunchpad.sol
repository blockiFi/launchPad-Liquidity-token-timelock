// File: @uniswap/v2-core/contracts/interfaces/IUniswapV2Factory.sol

pragma solidity >=0.5.0;

interface IUniswapV2Factory {
    event PairCreated(address indexed token0, address indexed token1, address pair, uint);

    function feeTo() external view returns (address);
    function feeToSetter() external view returns (address);

    function getPair(address tokenA, address tokenB) external view returns (address pair);
    function allPairs(uint) external view returns (address pair);
    function allPairsLength() external view returns (uint);

    function createPair(address tokenA, address tokenB) external returns (address pair);

    function setFeeTo(address) external;
    function setFeeToSetter(address) external;
}

// File: @uniswap/v2-core/contracts/interfaces/IUniswapV2Pair.sol

pragma solidity >=0.5.0;

interface IUniswapV2Pair {
    event Approval(address indexed owner, address indexed spender, uint value);
    event Transfer(address indexed from, address indexed to, uint value);

    function name() external pure returns (string memory);
    function symbol() external pure returns (string memory);
    function decimals() external pure returns (uint8);
    function totalSupply() external view returns (uint);
    function balanceOf(address owner) external view returns (uint);
    function allowance(address owner, address spender) external view returns (uint);

    function approve(address spender, uint value) external returns (bool);
    function transfer(address to, uint value) external returns (bool);
    function transferFrom(address from, address to, uint value) external returns (bool);

    function DOMAIN_SEPARATOR() external view returns (bytes32);
    function PERMIT_TYPEHASH() external pure returns (bytes32);
    function nonces(address owner) external view returns (uint);

    function permit(address owner, address spender, uint value, uint deadline, uint8 v, bytes32 r, bytes32 s) external;

    event Mint(address indexed sender, uint amount0, uint amount1);
    event Burn(address indexed sender, uint amount0, uint amount1, address indexed to);
    event Swap(
        address indexed sender,
        uint amount0In,
        uint amount1In,
        uint amount0Out,
        uint amount1Out,
        address indexed to
    );
    event Sync(uint112 reserve0, uint112 reserve1);

    function MINIMUM_LIQUIDITY() external pure returns (uint);
    function factory() external view returns (address);
    function token0() external view returns (address);
    function token1() external view returns (address);
    function getReserves() external view returns (uint112 reserve0, uint112 reserve1, uint32 blockTimestampLast);
    function price0CumulativeLast() external view returns (uint);
    function price1CumulativeLast() external view returns (uint);
    function kLast() external view returns (uint);

    function mint(address to) external returns (uint liquidity);
    function burn(address to) external returns (uint amount0, uint amount1);
    function swap(uint amount0Out, uint amount1Out, address to, bytes calldata data) external;
    function skim(address to) external;
    function sync() external;

    function initialize(address, address) external;
}

// File: @uniswap/v2-periphery/contracts/interfaces/IUniswapV2Router01.sol

pragma solidity >=0.6.2;

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
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountA, uint amountB);
    function removeLiquidityETHWithPermit(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
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
    function swapExactETHForTokens(uint amountOutMin, address[] calldata path, address to, uint deadline)
        external
        payable
        returns (uint[] memory amounts);
    function swapTokensForExactETH(uint amountOut, uint amountInMax, address[] calldata path, address to, uint deadline)
        external
        returns (uint[] memory amounts);
    function swapExactTokensForETH(uint amountIn, uint amountOutMin, address[] calldata path, address to, uint deadline)
        external
        returns (uint[] memory amounts);
    function swapETHForExactTokens(uint amountOut, address[] calldata path, address to, uint deadline)
        external
        payable
        returns (uint[] memory amounts);

    function quote(uint amountA, uint reserveA, uint reserveB) external pure returns (uint amountB);
    function getAmountOut(uint amountIn, uint reserveIn, uint reserveOut) external pure returns (uint amountOut);
    function getAmountIn(uint amountOut, uint reserveIn, uint reserveOut) external pure returns (uint amountIn);
    function getAmountsOut(uint amountIn, address[] calldata path) external view returns (uint[] memory amounts);
    function getAmountsIn(uint amountOut, address[] calldata path) external view returns (uint[] memory amounts);
}

// File: @uniswap/v2-periphery/contracts/interfaces/IUniswapV2Router02.sol

pragma solidity >=0.6.2;


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
        bool approveMax, uint8 v, bytes32 r, bytes32 s
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

// File: @openzeppelin/contracts/utils/Address.sol

pragma solidity >=0.6.2 <0.8.0;

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
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.

        uint256 size;
        // solhint-disable-next-line no-inline-assembly
        assembly { size := extcodesize(account) }
        return size > 0;
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
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{ value: amount }("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
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
      return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
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
    function functionCallWithValue(address target, bytes memory data, uint256 value, string memory errorMessage) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{ value: value }(data);
        return _verifyCallResult(success, returndata, errorMessage);
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
    function functionStaticCall(address target, bytes memory data, string memory errorMessage) internal view returns (bytes memory) {
        require(isContract(target), "Address: static call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.staticcall(data);
        return _verifyCallResult(success, returndata, errorMessage);
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
    function functionDelegateCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        require(isContract(target), "Address: delegate call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    function _verifyCallResult(bool success, bytes memory returndata, string memory errorMessage) private pure returns(bytes memory) {
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

// File: @openzeppelin/contracts/math/SafeMath.sol

pragma solidity >=0.6.0 <0.8.0;

/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryAdd(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        uint256 c = a + b;
        if (c < a) return (false, 0);
        return (true, c);
    }

    /**
     * @dev Returns the substraction of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function trySub(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        if (b > a) return (false, 0);
        return (true, a - b);
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryMul(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) return (true, 0);
        uint256 c = a * b;
        if (c / a != b) return (false, 0);
        return (true, c);
    }

    /**
     * @dev Returns the division of two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryDiv(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        if (b == 0) return (false, 0);
        return (true, a / b);
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryMod(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        if (b == 0) return (false, 0);
        return (true, a % b);
    }

    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");
        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b <= a, "SafeMath: subtraction overflow");
        return a - b;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        if (a == 0) return 0;
        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");
        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b > 0, "SafeMath: division by zero");
        return a / b;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b > 0, "SafeMath: modulo by zero");
        return a % b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {trySub}.
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        return a - b;
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {tryDiv}.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        return a / b;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting with custom message when dividing by zero.
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {tryMod}.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        return a % b;
    }
}

// File: contracts/libs/IBEP20.sol

pragma solidity >=0.4.0;

interface IBEP20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the token decimals.
     */
    function decimals() external view returns (uint8);

    /**
     * @dev Returns the token symbol.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the token name.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the bep token owner.
     */
    function getOwner() external view returns (address);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address _owner, address spender) external view returns (uint256);

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
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);

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
}

// File: @openzeppelin/contracts/utils/Context.sol

pragma solidity >=0.6.0 <0.8.0;

/*
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with GSN meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address payable) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes memory) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}

// File: @openzeppelin/contracts/access/Ownable.sol

pragma solidity >=0.6.0 <0.8.0;

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
    constructor ()  {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}


pragma solidity ^0.7.6;


 interface ILiquidityTimeLock {
     
    event liquidityLocked(address indexed pairAddress ,address indexed locker , address indexed owner ,  uint256 amount , uint256 unlockTime, uint256 lockID);
    event liquidityUnLocked(address indexed pairAddress, address indexed reciever , uint256 amount , uint256 lockID  );
    event liquidityMigrated(address indexed pairAddress, address indexed oldOwner , address indexed newOwner  , uint256 lockID  );
    
    function lockLiquidity(address _pairAddress ,address token1 , address token2  ,  uint256 amount ,  uint256 periodInHR , address _reciever ) external payable;
    
    function unLockLiquidity(address _pairAddress , uint256 lockID) external ;
    
    function migrateLiquidity(address _pairAddress , uint256 lockID , address to) external;
    
    function getActiveLPLockIDs(address _pairAddress) external view returns(uint256[] memory);
    
    function getTotalLocksValue(address _pairAddress)external view returns(uint256);
    function getTotalLocksBalance(address _pairAddress)external view returns(uint256);
    function getPairAddress(address token1 , address token2) external  view returns(address);
    function getTokens(address _pairAddress) external view returns(address token1 ,address token2);
    
   
}



pragma solidity ^0.7.6;


interface ItokenTimeLock{
  
   event tokenLocked(address indexed  tokenAddress ,address indexed locker , address indexed owner ,  uint256 amount , uint256 unlockTime, uint256 lockID);
    event tokenUnLocked(address indexed tokenAddress, address indexed reciever , uint256 amount , uint256 lockID  );
    event tokenMigrated(address indexed tokenAddress, address indexed oldOwner , address indexed newOwner  , uint256 lockID  );
   
    //provide either pair address or token1 and token2 address;
    function locktoken(address _tokenAddress  ,  uint256 amount ,  uint256 periodInHR , address _reciever ) external payable;
    
    
    
    function unLocktoken(address _tokenAddress , uint256 lockID) external;
    function migratetoken(address _tokenAddress , uint256 lockID , address to) external;
    
    function getActivetokenLockIDs(address _tokenAddress) external view returns(uint256[] memory);
    function getTotalLocksValue(address _tokenAddress)external view returns(uint256);
    function getTotalLocksBalance(address _tokenAddress)external view returns(uint256);

    function getUsertokenLocksAddress() external view returns(address[] memory);
   
    
}

// SPDX-License-Identifier: NULL

pragma solidity ^0.7.6;
pragma abicoder v2;

contract LaunchPad is Ownable{
    struct presaleBuyRecord {
        uint256 ethAmount;
        uint256 tokenAmount;
    }
    struct launch {
        address token;
        address pairAddress;
        address payable launchowner;
        uint256 AMMIndex;
        uint256 amountRaised;
        uint256 tokenBalance;
        uint256 tokenSold;
        
        
    }
   struct launchTimer {
       uint256 startTime;
        uint256 endTime;
        uint256 liquidityLockTime;
        uint256 presaleLockTime;  
    }
    struct launchRate{
         uint256 presaleRate;
        uint256 softCap;
        uint256 hardCap;
       uint256 minContribution;
        uint256 maxContribution;
        uint256 listTingRate;
        uint256 percentageLiquidity;
    }
    mapping (bytes32 => launch) public launchs;
    mapping (bytes32 => address[]) public whitelistedAddresses;
    mapping (bytes32 => mapping(address => bool) ) public iswhitelistedAddress;
     mapping (bytes32 =>bool) public  isPresaleLockActive;
    mapping (bytes32 => bool ) public isSet;
    mapping (bytes32 => bool ) public deposited;
    mapping (bytes32 => bool ) public successful;
    mapping (bytes32 => bool ) public whitelistEnabled;
    mapping (bytes32 => bool ) public completed;
    mapping (bytes32 => bool ) public ended;
    mapping(bytes32 => address[]) public presaleBuyers;
    mapping (bytes32 => mapping(address => presaleBuyRecord)) public presaleBuyRecords; 
    mapping(bytes32 => mapping(address => bool)) public isPresaleBuyer;
    mapping(bytes32 => launchTimer) public launchTimers;
    mapping(bytes32 => launchRate) public launchRates;
    mapping (address => bool)  public tokenLaunched;
    mapping (address => bool)  public tokenLaunchActive;
    mapping(address => bytes32 ) public tokenLaunchID;
    uint256 capSpacePercentage;
    uint256 systemMinContribution;
    uint256 systemMaxContribution;
    
    uint256 minStartTime;
     uint256 minEndTime;
     uint256 minLiquidityLockTime;
     uint256 minPercentageLiquidity;
     uint256 tresholdExtraRate;
     uint256 nounce;
     IUniswapV2Router02 testSwapRouter = IUniswapV2Router02(0x9Ac64Cc6e4415144C455BD8E4837Fea55603e5c3);
     ItokenTimeLock tokenTimeLocker ;
     ILiquidityTimeLock liquidityTimeLocker;
     address[] public AMM;
     function updateTresholdExtraRate(uint256 _tresholdExtraRate) public onlyOwner{
      require(_tresholdExtraRate <= 100 ,"invalid percentage" );
         tresholdExtraRate = _tresholdExtraRate;   
     }
     
     mapping(address => bool) public isAMM;
     function addAMM(address _amm ) public onlyOwner {
         require(!isAMM[_amm] , "already added");
         isAMM[_amm] = true;
         AMM.push(_amm);
     }
     function removeAMM(address _amm) public onlyOwner {
         require(isAMM[_amm] , "not added");
         for(uint256 index ; index <AMM.length; index++){
             if(AMM[index] == _amm){
                 AMM[index] = AMM[AMM.length-1];
                 AMM.pop();
                 isAMM[_amm] = false;
                 break;
                 
             }
         }
     }
     bytes32[] public openLaunchIDs;
     mapping(bytes32 => bool) public isopenLaunchID;
     struct lauchData {
         address tokenAddress ; 
        address payable tokenowner;
        uint256 _presaleRate;
        uint256 _softCap;
        uint256 _hardCap;
        uint256 _minContribution;
        uint256 _maxContribution;
        uint256 _listTingRate;
        uint256 _AMMIndex;
        uint256 _startTime;
        uint256 _endTime;
        uint256 _liquidityLockTime;
        uint256 _percentageLiquidity;
        bool _isPresaleLockActive;
        uint256 _presaleLockTime;
        bool _whitelistEnabled;
     }
       
   
     modifier onlyLaunchOwner(bytes32 launchAddress) {
         require(launchs[launchAddress].launchowner == _msgSender(), "unAthorized Access");
         _;
     }
     constructor (address timeLockerAddress , address liquidityLockerAddress){
          tokenTimeLocker = ItokenTimeLock(timeLockerAddress);
          liquidityTimeLocker =  ILiquidityTimeLock(liquidityLockerAddress);
          AMM.push(0x9Ac64Cc6e4415144C455BD8E4837Fea55603e5c3);
          isAMM[0x9Ac64Cc6e4415144C455BD8E4837Fea55603e5c3] = true;
     }
    //  ["0x7200704d8BFA013Aa129C0513953C7E2C0388C58","0x68d641560e7E50ce40E7eCb799Ae1FC197236e28","100000000000000000000000","1000000000000000000","2000000000000000000","10000000000000000","1000000000000000000","50000000000000000000000","0","1","5","9","70","true","4","false"] 
    function createLauch(lauchData memory data) public returns(bytes32) {
            // require(tokenowner !=address(0));
            require(tokenLaunchActive[data.tokenAddress] , "token launch already active");
            require(data._AMMIndex < AMM.length ,"invalid AMM index");
            address tokenPair = extractTokenPair(data.tokenAddress);
            checkCaps(data._softCap , data._hardCap);
            checkContributionLimits(data._minContribution , data._maxContribution);
            checkRates(data._presaleRate, data._listTingRate );
            checkTimer(data._startTime , data._endTime , data._liquidityLockTime);
            checkPercentageLiquidity(data._percentageLiquidity);
            bytes32 launchAddress = (keccak256(abi.encodePacked(block.timestamp, msg.sender, data.tokenAddress , tokenPair, nounce)));
           
          {
             
            
            require(!isSet[launchAddress]);
            
        isSet[launchAddress] = true;
          launch storage newLaunch = launchs[launchAddress];   
         newLaunch.token = data.tokenAddress;
         newLaunch.pairAddress = tokenPair;
         newLaunch.launchowner = data.tokenowner;
         newLaunch.AMMIndex = data._AMMIndex;
        
         launchTimer storage newLaunchTimer = launchTimers[launchAddress]; 
         newLaunchTimer.startTime = block.timestamp + ( data._startTime * 1 hours);
         newLaunchTimer.endTime = newLaunchTimer.startTime + (data._endTime * 1 hours);
         newLaunchTimer.liquidityLockTime = data._liquidityLockTime;
         newLaunchTimer.presaleLockTime = data._presaleLockTime;
     
         launchRate storage newlaunchRate = launchRates[launchAddress]; 
         newlaunchRate.presaleRate = data._presaleRate;
         newlaunchRate.softCap = data._softCap;
         newlaunchRate.hardCap = data._hardCap;
         newlaunchRate.minContribution = data._maxContribution;
         newlaunchRate.maxContribution = data._maxContribution;
         newlaunchRate.listTingRate = data._listTingRate;
         newlaunchRate.percentageLiquidity = data._percentageLiquidity;
        
         
         isPresaleLockActive[launchAddress]  = data._isPresaleLockActive;
          whitelistEnabled[launchAddress] = data._whitelistEnabled;
         
          }
          tokenLaunchActive[data.tokenAddress] = true;
          tokenLaunchID[data.tokenAddress] = launchAddress;
          openLaunchIDs.push(launchAddress);
          isopenLaunchID[launchAddress] = true;
         return launchAddress;  
        }
       //cancelLaunch
       
     function joinLaunch(bytes32 launchID , uint256 amount) public payable {
         require(msg.value >= amount , "insufficient funds");
        require(isSet[launchID] && deposited[launchID] &&  !completed[launchID] && !ended[launchID] , 'invalid launch');
        require(launchTimers[launchID].startTime < block.timestamp , "sales not started");
        require(launchs[launchID].amountRaised  < launchRates[launchID].hardCap && launchs[launchID].amountRaised + amount <= launchRates[launchID].hardCap 
        , "hard cap limit reached");
        require(amount >= launchRates[launchID].minContribution && amount <= launchRates[launchID].maxContribution , "amount out of contribution limits");
        
        if(whitelistEnabled[launchID]){
            require(iswhitelistedAddress[launchID][_msgSender()], "sender not whitelisted");
            
        }
        uint256 tokenValue = getTokenValue(launchID , amount);
        if(!isPresaleBuyer[launchID][_msgSender()]){
         presaleBuyers[launchID].push(_msgSender());
         isPresaleBuyer[launchID][_msgSender()] = true;
         
        }
        presaleBuyRecord storage buyerRecord = presaleBuyRecords[launchID][_msgSender()];
        buyerRecord.ethAmount += amount;
        buyerRecord.tokenAmount += tokenValue;
        
        launchs[launchID].amountRaised += amount;
        launchs[launchID].tokenSold += tokenValue;
        launchs[launchID].tokenBalance -= tokenValue;
     }
    function endLaunch(bytes32 launchID) public {
        require(isSet[launchID] && deposited[launchID] &&  !completed[launchID] && !ended[launchID] , 'invalid launch'); 
        require(launchTimers[launchID].startTime < block.timestamp , "sales not started");
        require(launchs[launchID].amountRaised >= launchRates[launchID].hardCap || launchTimers[launchID].endTime < block.timestamp , "EndLaunch requirements not satisfied");
        
        bool _successful;
        
        if(launchs[launchID].amountRaised >= launchRates[launchID].softCap ){
            _successful = true;
        }
        
        _endLaunch(launchID , _successful);
        
    }
    function _endLaunch(bytes32 launchID , bool _successful) private {
        if(_successful){
            endSucessfulLaunch(launchID);
            }else{
           launchs[launchID].tokenBalance += launchs[launchID].tokenSold;
           launchs[launchID].tokenSold = 0;
           IBEP20(launchs[launchID].token).transfer(launchs[launchID].launchowner , launchs[launchID].tokenBalance);
           launchs[launchID].tokenBalance = 0;  
          successful[launchID] =false;   
        }
        
        
        ended[launchID] =  true;
       
    }
    function endSucessfulLaunch(bytes32 launchID) private {
         uint256 liquidityToken =  (launchRates[launchID].listTingRate * launchRates[launchID].hardCap / 1 ether) * launchRates[launchID].percentageLiquidity / 100;
         launchs[launchID].tokenBalance -= liquidityToken;
        
         uint256 liquidityEth = launchs[launchID].amountRaised * launchRates[launchID].percentageLiquidity / 100;
          
         uint256 refundBalance = launchs[launchID].amountRaised - liquidityEth;
         
        
         IBEP20 pair = IBEP20(launchs[launchID].pairAddress);
        uint256 LpBalanceBefore = pair.balanceOf(address(this));
         addLiquidity(launchs[launchID].token , liquidityToken , liquidityEth);
        uint256 LpBalanceAfter = pair.balanceOf(address(this));
         //refund balance
         
         launchs[launchID].launchowner.transfer(refundBalance);
         IBEP20(launchs[launchID].token).transfer(launchs[launchID].launchowner , launchs[launchID].tokenBalance);
         launchs[launchID].tokenBalance = 0;
       
         //lock liquidity
         {
             IBEP20(launchs[launchID].pairAddress).approve(address(liquidityTimeLocker) , LpBalanceAfter - LpBalanceBefore );
         
         liquidityTimeLocker.lockLiquidity(
         launchs[launchID].pairAddress ,
         launchs[launchID].token , 
         testSwapRouter.WETH() ,  
          LpBalanceAfter - LpBalanceBefore,
         launchTimers[launchID].liquidityLockTime ,
         launchs[launchID].launchowner
         );
          
        successful[launchID] = true;
         }  
        
        }
    function claimToken(bytes32 launchID) public {
         require(isSet[launchID]  , 'invalid launch id');
         require(ended[launchID] , 'Launch not Ended');
         require(isPresaleBuyer[launchID][_msgSender()] , "not a presale buyer");
         
         if(isPresaleLockActive[launchID]){
            IBEP20(launchs[launchID].token).approve(address(tokenTimeLocker),presaleBuyRecords[launchID][_msgSender()].tokenAmount) ;
            tokenTimeLocker.locktoken(launchs[launchID].token, presaleBuyRecords[launchID][_msgSender()].tokenAmount  ,  launchTimers[launchID].presaleLockTime , _msgSender() ); 
             
         }
         else {
           IBEP20(launchs[launchID].token).transfer( _msgSender(),presaleBuyRecords[launchID][_msgSender()].tokenAmount);  
         }
         launchs[launchID].tokenSold -= presaleBuyRecords[launchID][_msgSender()].tokenAmount;
         isPresaleBuyer[launchID][_msgSender()] = false;
         for(uint256 index ; index < presaleBuyers[launchID].length ; index++){
             if(presaleBuyers[launchID][index] == _msgSender()){
                 presaleBuyers[launchID][index] == presaleBuyers[launchID][presaleBuyers[launchID].length-1];
                 presaleBuyers[launchID].pop();
                 break;
             }
         }
         
         if(presaleBuyers[launchID].length == 0){
             ended[launchID];
         }
          
    }
      function addLiquidity(address tokenAddress, uint256 tokenAmount, uint256 ethAmount) private {
        // approve token transfer to cover all possible scenarios
        IBEP20(tokenAddress).approve( address(testSwapRouter), tokenAmount);

        // add the liquidity
        testSwapRouter.addLiquidityETH{value: ethAmount}(
            tokenAddress,
            tokenAmount,
            0, // slippage is unavoidable
            0, // slippage is unavoidable
            address(this),
            block.timestamp
        );
    }
    function getTokenValue(bytes32 launchID, uint256 amount ) public view returns(uint256) {
      return  launchRates[launchID].presaleRate * amount / 1 ether;
    }
    function getDepositAmount(bytes32 launchAddress) public view returns(uint256) {
      uint256 presaleToken =  launchRates[launchAddress].presaleRate * launchRates[launchAddress].hardCap / 1 ether;
      uint256 liquidityToken =  (launchRates[launchAddress].listTingRate * launchRates[launchAddress].hardCap / 1 ether) * launchRates[launchAddress].percentageLiquidity / 100;
      uint256 tresholdExtra = (presaleToken + liquidityToken) * tresholdExtraRate / 100;
       
      return presaleToken + liquidityToken + tresholdExtra;
    }
    function depositToken(bytes32 launchAddress , uint256 amount) public onlyLaunchOwner(launchAddress) {
        require(!deposited[launchAddress], "token already deposited");
        
        uint256 requiredAmount  = getDepositAmount(launchAddress);
        require(amount >= requiredAmount , "amount less than requiredAmount");
        
        IBEP20 token = IBEP20(launchs[launchAddress].token);
        uint256 initialTokenBalance = token.balanceOf(address(this));
        token.transferFrom(_msgSender() , address(this) , amount);
        uint256 afterTokenBalance =  token.balanceOf(address(this));
        require(afterTokenBalance - initialTokenBalance >= requiredAmount);
        deposited[launchAddress] = true;
        
    }
    function extractTokenPair(address token) private returns(address){
        address weth = testSwapRouter.WETH();
        address pair = IUniswapV2Factory(testSwapRouter.factory()).getPair(token, weth);
        if(pair == address(0)){
          pair =  IUniswapV2Factory(testSwapRouter.factory()).createPair(token ,weth); 
        }
        return pair;
        
    }
    function checkPercentageLiquidity(uint256 _percentageLiquidity) private view {
        require(_percentageLiquidity <= 100 && _percentageLiquidity >= minPercentageLiquidity , "percentage liquidity lock error");
    }
    function checkCaps(uint256 _softCap , uint256 _hardCap) private view {
        require( _softCap != 0 && _hardCap != 0 , "zeros error");
        require(_hardCap > _softCap , "softCap greater than hardCap");
        require((_softCap * (capSpacePercentage/100)) <= _hardCap ,"softCap hardCap percenge difference error");
    }
    function checkContributionLimits(uint256 _minContribution , uint256 _maxContribution) private pure{
         require( _minContribution != 0 && _maxContribution != 0 , "zeros error"); 
         require(_maxContribution > _minContribution , "minContribution not less than maxContribution");
         
    }
    function checkRates(uint256 _presaleRate , uint256 listTingRate) private  pure{
        require( _presaleRate != 0 && listTingRate != 0 , "zeros error");
        require( _presaleRate > listTingRate , "presale rate should be greater than listing rate");
        
    }
    function  checkTimer(uint256 _startTime ,uint256 _endTime ,uint256 _liquidityLockTime) private view{
      require(_startTime >= minStartTime , "starttime less than default");
      require(_endTime >= minEndTime , "liquidity lock time less than default"); 
      require(_liquidityLockTime >= minLiquidityLockTime , "liquidity lock time less than default");  
     }
     function updateMinStartTime(uint256 _minStartTime) public onlyOwner{
         minStartTime = _minStartTime;
     }
      function updateMinEndTime(uint256 _minEndTime) public onlyOwner{
         minEndTime = _minEndTime;
     }
      function updateMinLiquidityLockTime(uint256 _minLiquidityLockTime) public onlyOwner{
         minLiquidityLockTime = _minLiquidityLockTime;
     }
      function updateSystemMinContribution(uint256 _systemMinContribution) public onlyOwner{
         systemMinContribution = _systemMinContribution;
     }
     function updateSystemMaxContribution(uint256 _systemMaxContribution) public onlyOwner{
         systemMaxContribution = _systemMaxContribution;
     }
     
     function updateCapSpacePercentage(uint256 _capSpacePercentage) public onlyOwner{
          
         capSpacePercentage = _capSpacePercentage;
     }
      function updateMinPercentageLiquidity(uint256 _minPercentageLiquidity) public onlyOwner{
          require(_minPercentageLiquidity <= 100 ,"invalid percentage" );
         minPercentageLiquidity = _minPercentageLiquidity;
     }
     
}