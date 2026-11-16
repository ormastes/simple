# Server context domain research

Reviewed official Kubernetes documentation on 2026-11-15:

- [Kubeconfig API](https://kubernetes.io/docs/reference/config-api/kubeconfig.v1/)
  separates named servers, credentials and contexts. The Simple design adopts
  named references while keeping credentials outside the server SDN.
- [Organizing cluster access](https://kubernetes.io/docs/concepts/configuration/organize-cluster-access-kubeconfig/)
  describes selected contexts. Simple retains a current context and explicit
  selection, then adds a per-consumer server override within that context.
- [Services](https://kubernetes.io/docs/concepts/services-networking/service/)
  describes DNS/environment discovery. Simple uses explicit advertised
  container endpoints; it does not imply Kubernetes service DNS exists.
- [DNS for Services and Pods](https://kubernetes.io/docs/concepts/services-networking/dns-pod-service/)
  documents scoped DNS and platform differences. Simple does not guess host
  aliases or equate host loopback with a container-reachable address.

These are design inferences from the primary references, not claims that Simple
implements Kubernetes service discovery or an authenticated HTTPS API.
