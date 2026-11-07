#!/usr/bin/env python3
"""Small illustrative checks for deadline boundaries and a reset fault.

The faulty policy is an artificial counterexample model. It is not CASAAL,
Spot, or code from the verified development.
"""


def every_request_has_timely_ack(request_times, ack_times, deadline, *, strict=False):
    compare = (lambda age: age < deadline) if strict else (lambda age: age <= deadline)
    return all(
        any(ack >= request and compare(ack - request) for ack in ack_times)
        for request in request_times
    )


def reset_single_clock_on_each_request(request_times, ack_times, deadline):
    """Intentionally incorrect: one clock is restarted by each new request."""
    last_request = None
    requests = iter(request_times)
    next_request = next(requests, None)
    for event_time in sorted(set(request_times) | set(ack_times)):
        if event_time == next_request:
            last_request = event_time
            next_request = next(requests, None)
        if event_time in ack_times and last_request is not None:
            if event_time - last_request <= deadline:
                return True
    return False


def main():
    # Same essential times as alarm_response_trace: requests at 0 and 2,
    # one response at 4, and deadline 3. The first request is already late.
    requests, acknowledgments, deadline = [0, 2], [4], 3
    correct = every_request_has_timely_ack(requests, acknowledgments, deadline)
    faulty = reset_single_clock_on_each_request(requests, acknowledgments, deadline)
    assert correct is False
    assert faulty is True

    # At the exact endpoint, non-strict <= accepts and strict < rejects.
    endpoint_nonstrict = every_request_has_timely_ack([0], [3], 3, strict=False)
    endpoint_strict = every_request_has_timely_ack([0], [3], 3, strict=True)
    assert endpoint_nonstrict is True
    assert endpoint_strict is False

    print("PASS: queue-based response check rejects requests=[0,2], ack=[4], d=3")
    print("PASS: intentionally faulty reset-on-each-request model accepts the same trace")
    print("PASS: at t=d, <=d accepts while <d rejects")
    print("LIMIT: finite illustrative scenario only; not a Rocq theorem, not an implementation of CASAAL, and not a claim about prior tools")


if __name__ == "__main__":
    main()
