package click.nullpointer.genaidafny.openai.helpers;

import java.net.http.HttpHeaders;
import java.time.Duration;
import java.time.Instant;
import java.util.Objects;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.TimeUnit;

public class OpenAIRateLimiter {
    private final RateLimitingPolicy policy;
    private long resetAt;

    /**
     * Package private constructor. Create an {@link OpenAIRateLimiter} with a specified {@link RateLimitingPolicy}.
     *
     * @param policy The {@link RateLimitingPolicy} to apply. Must not be null.
     */
    public OpenAIRateLimiter(RateLimitingPolicy policy) {
        Objects.requireNonNull(policy);
        this.policy = policy;
    }

    /**
     * Get the remaining time until the rate limit expires.
     *
     * @return The remaining time in milliseconds, or 0 if no rate limiting applies.
     */
    public synchronized long getRateLimitDurationMillis() {
        if (resetAt == 0)
            return 0;
        long del = Duration.between(Instant.now(), Instant.ofEpochSecond(resetAt)).toMillis();
        return Math.max(0, del);
    }

    /**
     * Check if a rate limitation applies.
     *
     * @return true if a delay applies before a subsequent request can be made, false otherwise.
     */
    public synchronized boolean isRateLimited() {
        return getRateLimitDurationMillis() == 0;
    }

    /**
     * Update rate limits based on {@link HttpHeaders}.
     * This method only reads the x-ratelimit-reset header of {@link HttpHeaders}. To set the value of this header manually, see
     * {@link #updateRateLimit(long)}.
     *
     * @param responseHeaders The {@link HttpHeaders} on which an x-ratelimit-reset may be set.
     */
    public synchronized void updateRateLimit(HttpHeaders responseHeaders) {
        Objects.requireNonNull(responseHeaders);
        String rateLimitReset = responseHeaders.firstValue("x-ratelimit-reset").orElse(null);
        if (rateLimitReset != null) {
            resetAt = Long.parseLong(rateLimitReset);
        } else {
            resetAt = Instant.now().getEpochSecond();
        }
    }

    /**
     * Set the rate limit reset timestamp, in epoch seconds.
     * If the given reset timestamp is in the past, this call has no effect.
     * If the current reset timestamp is later than the given reset timestamp, an immediate reset is applied (rate limit cleared).
     *
     * @param resetAtEpochSeconds The timestamp at which the rate limit resets.
     */
    public synchronized void updateRateLimit(long resetAtEpochSeconds) {
        long now = Instant.now().getEpochSecond();
        if (now > resetAtEpochSeconds)
            return;
        resetAt = resetAtEpochSeconds;
    }

    /**
     * Constructs a base {@link CompletableFuture} of the specified type, with actions relevant to the selected
     * {@link RateLimitingPolicy} attached.
     * The behaviour of the returned {@link CompletableFuture} may range from a delay in execution, to a failed {@link CompletableFuture}
     * or even an exception being raised by this call.
     * If a {@link CompletableFuture} is returned, it should be used as the basis of a chain of other completion stages, to run after it
     * (synchronously or not).
     *
     * @param <T> The desired {@link CompletableFuture} type.
     * @return A {@link CompletableFuture} with the relevant actions applied.
     * @throws RateLimitedException if the specified policy of this object is {@link RateLimitingPolicy#EXCEPTION}
     */
    public <T> CompletableFuture<T> getRateLimitingBase() {
        CompletableFuture<T> base = null;
        //If rate limited, schedule a dummy execution that is delayed accordingly.
        if (isRateLimited()) {
            if (policy == RateLimitingPolicy.DELAY_REQUEST) {
                base = CompletableFuture.supplyAsync(() -> null, CompletableFuture.delayedExecutor(getRateLimitDurationMillis(),
                        TimeUnit.MILLISECONDS));
            } else if (policy == RateLimitingPolicy.COMPLETE_EXCEPTIONALLY) {
                return CompletableFuture.failedFuture(new RateLimitedException("Rate limited", getRateLimitDurationMillis()));
            } else if (policy == RateLimitingPolicy.EXCEPTION) {
                throw new RateLimitedException("Rate limited", getRateLimitDurationMillis());
            }
        } else {
            //Else use a completed future, to just tag on to (dumy)
            base = CompletableFuture.completedFuture(null);
        }
        return base;
    }

    /**
     * A range of policies dictating the handling of an active rate limit.
     */
    public enum RateLimitingPolicy {
        //Set requests to be delayed, until the rate limit expires.
        /**
         * Delay any future request until the rate limit has expired.
         */
        DELAY_REQUEST,
        // Complete the future exceptionally straight away
        /**
         * Complete a future operation exceptionally and outright if a rate limit is applicable.
         */
        COMPLETE_EXCEPTIONALLY,
        // Throw a conventional runtime exception without attempting to schedule anytihng.
        /**
         * Trigger an exception at the time of discovery of an active rate limit, without creating further future work.
         */
        EXCEPTION;
    }

    public class RateLimitedException extends RuntimeException {
        private final long rateLimitForMs;

        /**
         * Construct a rate limit exception with a predefined message and expirty time.
         *
         * @param message        The message.
         * @param rateLimitForMs The expected expiry of the rate limitation as an epoch second timestamp.
         */
        public RateLimitedException(String message, long rateLimitForMs) {
            super(message);
            this.rateLimitForMs = rateLimitForMs;
        }

        /**
         * Get the expected expiry of the rate limit as a timestamp.
         *
         * @return The timestamp as seconds since epoch.
         */
        public long getRateLimitForMs() {
            return rateLimitForMs;
        }
    }

}
