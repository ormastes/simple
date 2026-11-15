FROM busybox:1.36
# Both image defaults fail. The session's exact command must replace them.
ENTRYPOINT ["/bin/false"]
CMD ["/bin/false"]
