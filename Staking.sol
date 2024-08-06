// stake: Lock tokens into our smart contract (Synthetix version?)
// withdraw: unlock tokens from our smart contract
// claimReward: users get their reward tokens
//      What's a good reward mechanism?
//      What's some good reward math?

// Added functionality ideas: Use users funds to fund liquidity pools to make income from that?

// SPDX-License-Identifier: MIT

pragma solidity >=0.8.0 <0.9.0;

import "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import "@openzeppelin/contracts/security/ReentrancyGuard.sol";

error Staking__TransferFailed();
error Withdraw__TransferFailed();
error Staking__NeedsMoreThanZero();

contract Staking is ReentrancyGuard {
    IERC20 public s_stakingToken;
    IERC20 public s_rewardToken;

    uint256 public s_totalSupply;

    /** @dev Mapping from address to the amount the user has staked */
    mapping(address => uint256) public s_balances;

    /** @dev Mapping from address to the rewards claimable for user */
    mapping(address => uint256) public s_rewards;

    // 10% annual reward
    uint public constant ANNUAL_REWARD_PERCENTAGE = 10;
    uint public constant SECONDS_IN_A_YEAR = 365 * 24 * 60 * 60;


    modifier updateReward(address account) {
        s_rewards[account] = earned(account);
        s_balances[account] = block.timestamp;
        _;
    }

    modifier moreThanZero(uint256 amount) {
        if (amount == 0) {
            revert Staking__NeedsMoreThanZero();
        }
        _;
    }

    constructor(address stakingToken, address rewardToken) {
        s_stakingToken = IERC20(stakingToken);
        s_rewardToken = IERC20(rewardToken);
    }

    function earned(address account) public view returns (uint256) {
        uint256 stakedAmount = s_balances[account];
        uint256 lastRewardTime = s_balances[account];
        uint256 stakedDuration = block.timestamp - lastRewardTime;

        uint256 annualReward = (stakedAmount * ANNUAL_REWARD_PERCENTAGE) / 100;
        uint256 earnedReward = (annualReward * stakedDuration) / SECONDS_IN_A_YEAR;

        return earnedReward + s_rewards[account];
    }

    function stake(uint256 amount) external updateReward(msg.sender) moreThanZero(amount) {
        // keep track of how much this user has staked
        // keep track of how much token we have total
        // transfer the tokens to this contract
        /** @notice Be mindful of reentrancy attack here */
        s_balances[msg.sender] += amount;
        s_totalSupply += amount;
        //emit event
        bool success = s_stakingToken.transferFrom(msg.sender, address(this), amount);
        // require(success, "Failed"); Save gas fees here
        if (!success) {
            revert Staking__TransferFailed();
        }
    }

    function withdraw(uint256 amount) external updateReward(msg.sender) moreThanZero(amount) {
        s_balances[msg.sender] -= amount;
        s_totalSupply -= amount;
        // emit event
        bool success = s_stakingToken.transfer(msg.sender, amount);
        if (!success) {
            revert Withdraw__TransferFailed();
        }
    }

    function claimReward() external updateReward(msg.sender) {
        uint256 reward = s_rewards[msg.sender];
        bool success = s_rewardToken.transfer(msg.sender, reward);
        if (!success) {
            revert Staking__TransferFailed();
        }
    }

    // Getter for UI
    function getStaked(address account) public view returns (uint256) {
        return s_balances[account];
    }
}